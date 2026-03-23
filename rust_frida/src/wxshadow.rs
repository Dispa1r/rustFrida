#![cfg(all(target_os = "android", target_arch = "aarch64"))]

use std::fs;
use std::mem::size_of;
use std::process::Command;

const PR_WXSHADOW_SET_OFFSETS: libc::c_int = 0x5758_0009;

const WXSHADOW_OFFSET_SYNC_MAGIC: u32 = 0x5758_4254;
const WXSHADOW_OFFSET_VALID_VM_MM: u16 = 1 << 0;
const WXSHADOW_OFFSET_VALID_MM_PGD: u16 = 1 << 1;

const DEFAULT_BTF_PATH: &str = "/sys/kernel/btf/vmlinux";

const BTF_MAGIC: u16 = 0xeb9f;

const BTF_KIND_INT: u32 = 1;
const BTF_KIND_PTR: u32 = 2;
const BTF_KIND_ARRAY: u32 = 3;
const BTF_KIND_STRUCT: u32 = 4;
const BTF_KIND_UNION: u32 = 5;
const BTF_KIND_ENUM: u32 = 6;
const BTF_KIND_FWD: u32 = 7;
const BTF_KIND_TYPEDEF: u32 = 8;
const BTF_KIND_VOLATILE: u32 = 9;
const BTF_KIND_CONST: u32 = 10;
const BTF_KIND_RESTRICT: u32 = 11;
const BTF_KIND_FUNC: u32 = 12;
const BTF_KIND_FUNC_PROTO: u32 = 13;
const BTF_KIND_VAR: u32 = 14;
const BTF_KIND_DATASEC: u32 = 15;
const BTF_KIND_FLOAT: u32 = 16;
const BTF_KIND_DECL_TAG: u32 = 17;
const BTF_KIND_TYPE_TAG: u32 = 18;
const BTF_KIND_ENUM64: u32 = 19;

#[repr(C)]
struct WxshadowOffsetSync {
    magic: u32,
    size: u16,
    flags: u16,
    vm_area_vm_mm_offset: i16,
    mm_struct_pgd_offset: i16,
    reserved0: i16,
    reserved1: i16,
}

pub(crate) enum SyncResult {
    Synced { vm_mm: i16, pgd: i16 },
    NotAvailable,
}

fn read_u16_le(data: &[u8], off: usize) -> Option<u16> {
    let bytes = data.get(off..off + 2)?;
    Some(u16::from_le_bytes([bytes[0], bytes[1]]))
}

fn read_u32_le(data: &[u8], off: usize) -> Option<u32> {
    let bytes = data.get(off..off + 4)?;
    Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

fn btf_extra_len(kind: u32, vlen: u32) -> Option<usize> {
    match kind {
        BTF_KIND_INT => Some(4),
        BTF_KIND_PTR | BTF_KIND_FWD | BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST
        | BTF_KIND_RESTRICT | BTF_KIND_FUNC | BTF_KIND_FLOAT | BTF_KIND_TYPE_TAG => Some(0),
        BTF_KIND_ARRAY => Some(12),
        BTF_KIND_STRUCT | BTF_KIND_UNION => Some(vlen as usize * 12),
        BTF_KIND_ENUM => Some(vlen as usize * 8),
        BTF_KIND_FUNC_PROTO => Some(vlen as usize * 8),
        BTF_KIND_VAR => Some(4),
        BTF_KIND_DATASEC => Some(vlen as usize * 12),
        BTF_KIND_DECL_TAG => Some(4),
        BTF_KIND_ENUM64 => Some(vlen as usize * 12),
        _ => None,
    }
}

fn btf_string(strings: &[u8], off: u32) -> Option<&str> {
    let off = off as usize;
    let tail = strings.get(off..)?;
    let nul = tail.iter().position(|b| *b == 0)?;
    std::str::from_utf8(&tail[..nul]).ok()
}

fn find_struct_member_offset(blob: &[u8], struct_name: &str, member_name: &str) -> Result<i16, String> {
    if blob.len() < 24 {
        return Err("BTF blob too small".into());
    }

    let magic = read_u16_le(blob, 0).ok_or("missing BTF magic")?;
    if magic != BTF_MAGIC {
        return Err(format!("bad BTF magic: 0x{magic:04x}"));
    }

    let hdr_len = read_u32_le(blob, 4).ok_or("missing hdr_len")? as usize;
    let type_off = read_u32_le(blob, 8).ok_or("missing type_off")? as usize;
    let type_len = read_u32_le(blob, 12).ok_or("missing type_len")? as usize;
    let str_off = read_u32_le(blob, 16).ok_or("missing str_off")? as usize;
    let str_len = read_u32_le(blob, 20).ok_or("missing str_len")? as usize;

    let types_start = hdr_len + type_off;
    let types_end = types_start + type_len;
    let strs_start = hdr_len + str_off;
    let strs_end = strs_start + str_len;

    let types = blob
        .get(types_start..types_end)
        .ok_or("BTF type section out of range")?;
    let strings = blob
        .get(strs_start..strs_end)
        .ok_or("BTF string section out of range")?;

    let mut off = 0usize;
    while off + 12 <= types.len() {
        let name_off = read_u32_le(types, off).ok_or("bad type name_off")?;
        let info = read_u32_le(types, off + 4).ok_or("bad type info")?;
        let _size_type = read_u32_le(types, off + 8).ok_or("bad type size_type")?;
        let kind = (info >> 24) & 0x1f;
        let vlen = info & 0xffff;
        let extra_len = btf_extra_len(kind, vlen).ok_or_else(|| format!("unsupported BTF kind {kind}"))?;
        let rec_end = off + 12 + extra_len;
        if rec_end > types.len() {
            return Err("BTF type record truncated".into());
        }

        if kind == BTF_KIND_STRUCT || kind == BTF_KIND_UNION {
            if let Some(name) = btf_string(strings, name_off) {
                if name == struct_name {
                    let mut member_off = off + 12;
                    for _ in 0..vlen {
                        let member_name_off =
                            read_u32_le(types, member_off).ok_or("bad member name_off")?;
                        let _member_type =
                            read_u32_le(types, member_off + 4).ok_or("bad member type")?;
                        let member_bit_off =
                            read_u32_le(types, member_off + 8).ok_or("bad member offset")?;
                        if let Some(mname) = btf_string(strings, member_name_off) {
                            if mname == member_name {
                                return Ok((member_bit_off / 8) as i16);
                            }
                        }
                        member_off += 12;
                    }
                    return Err(format!("member {struct_name}.{member_name} not found"));
                }
            }
        }

        off = rec_end;
    }

    Err(format!("struct {struct_name} not found"))
}

fn read_btf_blob() -> Result<Vec<u8>, String> {
    if let Ok(data) = fs::read(DEFAULT_BTF_PATH) {
        return Ok(data);
    }

    let output = Command::new("su")
        .args(["-c", "cat /sys/kernel/btf/vmlinux"])
        .output()
        .map_err(|e| format!("failed to invoke su for BTF read: {e}"))?;

    if !output.status.success() {
        return Err(format!(
            "failed to read BTF via su: status={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }

    Ok(output.stdout)
}

pub(crate) fn auto_sync_offsets() -> Result<SyncResult, String> {
    let blob = match read_btf_blob() {
        Ok(blob) => blob,
        Err(err) => return Err(format!("read BTF failed: {err}")),
    };

    let vm_mm = find_struct_member_offset(&blob, "vm_area_struct", "vm_mm")?;
    let pgd = find_struct_member_offset(&blob, "mm_struct", "pgd")?;

    let cfg = WxshadowOffsetSync {
        magic: WXSHADOW_OFFSET_SYNC_MAGIC,
        size: size_of::<WxshadowOffsetSync>() as u16,
        flags: WXSHADOW_OFFSET_VALID_VM_MM | WXSHADOW_OFFSET_VALID_MM_PGD,
        vm_area_vm_mm_offset: vm_mm,
        mm_struct_pgd_offset: pgd,
        reserved0: 0,
        reserved1: 0,
    };

    let ret = unsafe {
        libc::prctl(
            PR_WXSHADOW_SET_OFFSETS,
            &cfg as *const WxshadowOffsetSync as libc::c_ulong,
            0,
            0,
            0,
        )
    };

    if ret == 0 {
        return Ok(SyncResult::Synced { vm_mm, pgd });
    }

    let err = std::io::Error::last_os_error();
    let errno = err.raw_os_error().unwrap_or_default();

    if matches!(errno, libc::EINVAL | libc::ENOSYS | libc::ENOTTY) {
        return Ok(SyncResult::NotAvailable);
    }

    Err(format!("prctl(PR_WXSHADOW_SET_OFFSETS) failed: {err}"))
}
