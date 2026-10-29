use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

fn find_elan_tool(tool_name: &str) -> Option<PathBuf> {
    if let Ok(explicit) = env::var("LEANSYS_LEAN") {
        let path = PathBuf::from(explicit);
        if path.is_file() && path.file_name().and_then(|s| s.to_str()) == Some(tool_name) {
            return Some(path);
        }
    }
    if let Ok(explicit) = env::var("ORB_LEAN") {
        let path = PathBuf::from(explicit);
        if path.is_file() && path.file_name().and_then(|s| s.to_str()) == Some(tool_name) {
            return Some(path);
        }
    }
    if let Ok(path_var) = env::var("PATH") {
        for dir in env::split_paths(&path_var) {
            let cand = dir.join(tool_name);
            if cand.is_file() {
                return Some(cand);
            }
        }
    }
    let mut roots = Vec::new();
    if let Ok(elan_home) = env::var("ELAN_HOME") {
        roots.push(PathBuf::from(elan_home));
    }
    if let Ok(home) = env::var("HOME") {
        roots.push(PathBuf::from(home).join(".elan"));
    }
    roots.push(PathBuf::from("/var/lib/orb-node/work/caches/elan"));
    roots.push(PathBuf::from("/var/lib/sandboxed-node/caches/elan"));
    for root in roots {
        let bin_cand = root.join("bin").join(tool_name);
        if bin_cand.is_file() {
            return Some(bin_cand);
        }
        let tc_dir = root.join("toolchains");
        if let Ok(entries) = fs::read_dir(&tc_dir) {
            for entry in entries.flatten() {
                let cand = entry.path().join("bin").join(tool_name);
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

const LEANSYS_EXPORTS: &[&str] = &[
    "leansys_verify_slice_bounds",
    "leansys_verify_wal_frame",
    "leansys_verify_cas_digest",
    "leansys_check_http_bounds",
    "leansys_verify_jsonl_tape",
    "leansys_verify_ring_cursor",
    "leansys_verify_sst_block",
    "leansys_verify_poll_interest",
    "leansys_verify_rlimit_budget",
    "leansys_mix64_word",
    "leansys_verify_composite_key_order",
    "leansys_verify_token_auth",
    "leansys_verify_log_window",
    "leansys_verify_jsonrpc_frame",
    "leansys_gate_admit",
    "leansys_verify_mmap_seqlock",
    "leansys_verify_proc_stat_fields",
    "leansys_sse_frame_scan",
    "leansys_gfm_pipe_scan",
    "leansys_tag_scan",
    "leansys_transcript_index",
    "leansys_verify_par_chunk",
    "leansys_verify_arena_disjoint",
    "leansys_verify_snapshot_visibility",
    "leansys_verify_http_route_match",
    "leansys_verify_counterexample_triage",
    "leansys_verify_dag_wave_step",
    "leansys_verify_ios_jetsam_budget",
    "leansys_verify_worker_budget",
    "leansys_verify_page_aligned_buffer",
    "leansys_select_isa",
    "leansys_verify_isa_selection",
    "leansys_verify_fd_bounds",
];

fn extract_spec_exports(spec_src: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in spec_src.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("@[inline, export ") {
            if let Some(sym) = rest.strip_suffix(']') {
                out.push(sym.trim().to_string());
            }
        }
    }
    out
}

fn build_lean_sys_cabi(root: &Path, out_dir: &Path) {
    println!(
        "cargo:rerun-if-changed={}",
        root.join("LeanSys/Spec.lean").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        root.join("LeanSys/Gate.lean").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        root.join("LeanSys/Contracts/MetaGate.lean").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        root.join("LeanSys/Contracts/SpeculativeGate.lean")
            .display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        root.join("lean-toolchain").display()
    );

    let spec_src = fs::read_to_string(root.join("LeanSys/Spec.lean"))
        .unwrap_or_else(|e| panic!("failed to read LeanSys/Spec.lean: {e}"));
    let spec_exports = extract_spec_exports(&spec_src);
    assert_eq!(
        spec_exports,
        LEANSYS_EXPORTS
            .iter()
            .map(|s| (*s).to_string())
            .collect::<Vec<_>>(),
        "build.rs LEANSYS_EXPORTS drifted from @[inline, export ...] in LeanSys/Spec.lean"
    );

    let out_contracts_dir = out_dir.join("LeanSys").join("Contracts");
    fs::create_dir_all(&out_contracts_dir)
        .unwrap_or_else(|e| panic!("failed to create {}: {e}", out_contracts_dir.display()));
    let out_leansys_dir = out_dir.join("LeanSys");

    let metagate_olean = out_contracts_dir.join("MetaGate.olean");
    let specgate_olean = out_contracts_dir.join("SpeculativeGate.olean");
    let gate_olean = out_leansys_dir.join("Gate.olean");
    let spec_olean = out_leansys_dir.join("Spec.olean");
    let spec_c_path = out_dir.join("LeanSys_Spec.c");
    let obj_path = out_dir.join("LeanSys_Spec.o");
    let gc_obj_path = out_dir.join("LeanSys_Spec_gc.o");
    let lib_path = out_dir.join("liblean_sys_cabi.a");

    let lean_bin = find_elan_tool("lean").unwrap_or_else(|| {
        panic!("lean not found; set LEANSYS_LEAN or install elan (leanprover/lean4:v4.35.0)")
    });

    for (src, olean) in [
        ("LeanSys/Contracts/MetaGate.lean", &metagate_olean),
        ("LeanSys/Contracts/SpeculativeGate.lean", &specgate_olean),
        ("LeanSys/Gate.lean", &gate_olean),
    ] {
        let st = Command::new(&lean_bin)
            .current_dir(root)
            .env("LEAN_PATH", out_dir)
            .arg(src)
            .arg("-o")
            .arg(olean)
            .status()
            .unwrap_or_else(|e| panic!("failed to run lean on {src}: {e}"));
        assert!(st.success() && olean.is_file(), "lean failed on {src}");
    }

    let spec_status = Command::new(&lean_bin)
        .current_dir(root)
        .env("LEAN_PATH", out_dir)
        .arg("LeanSys/Spec.lean")
        .arg("-o")
        .arg(&spec_olean)
        .arg("-c")
        .arg(&spec_c_path)
        .status()
        .unwrap_or_else(|e| panic!("failed to run lean on LeanSys/Spec.lean: {e}"));
    assert!(
        spec_status.success() && spec_c_path.is_file(),
        "lean failed to compile LeanSys/Spec.lean to C (0 sorryAx required)"
    );

    let lean_prefix = Command::new(&lean_bin)
        .current_dir(root)
        .arg("--print-prefix")
        .output()
        .unwrap_or_else(|e| panic!("lean --print-prefix failed: {e}"));
    assert!(lean_prefix.status.success(), "lean --print-prefix failed");
    let prefix = String::from_utf8_lossy(&lean_prefix.stdout)
        .trim()
        .to_string();
    let include = PathBuf::from(&prefix).join("include");

    let macos = env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos");
    let compile_c_path = if macos {
        let src = fs::read_to_string(&spec_c_path).expect("read LeanSys_Spec.c");
        let mut c = String::with_capacity(src.len());
        for line in src.lines() {
            let name = line
                .strip_prefix("LEAN_EXPORT ")
                .and_then(|rest| rest.split('(').next())
                .and_then(|head| {
                    head.rsplit(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
                        .next()
                });
            match name {
                Some(n) if !LEANSYS_EXPORTS.contains(&n) => {
                    c.push_str("static ");
                    c.push_str(&line["LEAN_EXPORT ".len()..]);
                }
                _ => c.push_str(line),
            }
            c.push('\n');
        }
        let path = out_dir.join("LeanSys_Spec_macos.c");
        fs::write(&path, c).expect("write LeanSys_Spec_macos.c");
        path
    } else {
        spec_c_path.clone()
    };

    let mut compiled = false;
    for compiler in ["cc", "clang", "gcc"] {
        if let Ok(st) = Command::new(compiler)
            .args([
                "-O3",
                "-fPIC",
                "-ffunction-sections",
                "-fdata-sections",
                "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg(&compile_c_path)
            .arg("-o")
            .arg(&obj_path)
            .status()
        {
            if st.success() && obj_path.is_file() {
                compiled = true;
                break;
            }
        }
    }
    assert!(compiled, "failed to compile LeanSys/Spec.c");

    if macos {
        fs::copy(&obj_path, &gc_obj_path).expect("copy LeanSys_Spec.o");
        let _ = Command::new("strip").arg("-x").arg(&gc_obj_path).status();
    } else {
        let mut ld_args = vec!["-r".to_string(), "--gc-sections".to_string()];
        for sym in LEANSYS_EXPORTS {
            ld_args.push("-u".to_string());
            ld_args.push((*sym).to_string());
        }
        ld_args.push(obj_path.display().to_string());
        ld_args.push("-o".to_string());
        ld_args.push(gc_obj_path.display().to_string());
        let ld_status = Command::new("ld")
            .args(&ld_args)
            .status()
            .unwrap_or_else(|e| panic!("ld --gc-sections failed: {e}"));
        assert!(
            ld_status.success() && gc_obj_path.is_file(),
            "ld --gc-sections failed"
        );
        let _ = Command::new("strip")
            .args(["--strip-unneeded"])
            .arg(&gc_obj_path)
            .status();
    }

    let nm_out = Command::new("nm")
        .args(["-P", "-u"])
        .arg(&gc_obj_path)
        .output()
        .unwrap_or_else(|e| panic!("nm failed: {e}"));
    let undefined = String::from_utf8_lossy(&nm_out.stdout);
    assert!(
        undefined.trim().is_empty(),
        "LeanSys C-ABI object has undefined symbols:\n{undefined}"
    );
    let defined = Command::new("nm")
        .args(["-P"])
        .arg(&gc_obj_path)
        .output()
        .unwrap_or_else(|e| panic!("nm failed: {e}"));
    let defined_text = String::from_utf8_lossy(&defined.stdout);
    for sym in LEANSYS_EXPORTS {
        assert!(
            defined_text.lines().any(|line| {
                let mut parts = line.split_whitespace();
                let name = parts.next().map(|n| {
                    if macos {
                        n.strip_prefix('_').unwrap_or(n)
                    } else {
                        n
                    }
                });
                name == Some(*sym) && parts.next() == Some("T")
            }),
            "missing defined export {sym}"
        );
    }

    let mut archived = false;
    for ar_tool in ["llvm-ar", "ar"] {
        if let Ok(st) = Command::new(ar_tool)
            .arg("rcs")
            .arg(&lib_path)
            .arg(&gc_obj_path)
            .status()
        {
            if st.success() && lib_path.is_file() {
                archived = true;
                break;
            }
        }
    }
    assert!(archived, "failed to archive liblean_sys_cabi.a");
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=lean_sys_cabi");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lib.rs");
    let manifest_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    build_lean_sys_cabi(&manifest_dir, &out_dir);
}
