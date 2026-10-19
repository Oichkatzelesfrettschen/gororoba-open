use std::{env, fs, path::PathBuf, process::Command};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = env::args().skip(1);
    let proof_root = PathBuf::from(arguments.next().ok_or("missing proof root")?);
    let output_root = PathBuf::from(arguments.next().ok_or("missing output root")?);
    if arguments.next().is_some() {
        return Err("unexpected argument".into());
    }
    fs::create_dir_all(&output_root)?;
    let source = fs::read_to_string(
        proof_root.join("checkpoints/schur-geometry/SchurAccelerationObstruction.v"),
    )?;
    let compile = |name: &str, contents: &str| -> Result<bool, Box<dyn std::error::Error>> {
        let path = output_root.join(format!("{name}.v"));
        fs::write(&path, contents)?;
        let result = Command::new("opam")
            .args([
                "exec",
                "--switch=rocq-9.3",
                "--",
                "rocq",
                "compile",
                "-q",
                "-w",
                "+default",
                "-Q",
            ])
            .arg(proof_root.join("theories"))
            .arg("OpenGororoba")
            .arg(&path)
            .output()?;
        let mut retained_log = result.stdout;
        retained_log.extend_from_slice(&result.stderr);
        fs::write(output_root.join(format!("{name}.log")), retained_log)?;
        println!("{name}: {}", result.status);
        Ok(result.status.success())
    };
    if !compile("UnalteredLaw", &source)? {
        return Err("unaltered law failed; mutation rejection is inconclusive".into());
    }
    let mutations = [
        (
            "AnnihilatorTargetSwap",
            "separator *m derivative = 0 -> separator *m target <> 0 ->",
            "separator *m derivative = separator *m derivative -> separator *m target <> 0 ->",
        ),
        (
            "WrongRadialSign",
            "(- norm_acceleration_residual center velocity acceleration /",
            "(norm_acceleration_residual center velocity acceleration /",
        ),
        (
            "RadialDerivativeTarget",
            "derivative *m center = 0 ->",
            "derivative *m center = target ->",
        ),
        (
            "ZeroCenterDomain",
            "real_column_pairing center center <> 0%R ->",
            "real_column_pairing center center = 0%R ->",
        ),
    ];
    for (name, before, after) in mutations {
        if !source.contains(before) {
            return Err(format!("missing mutation anchor: {name}").into());
        }
        if compile(name, &source.replacen(before, after, 1))? {
            return Err(format!("altered law accepted: {name}").into());
        }
    }
    Ok(())
}
