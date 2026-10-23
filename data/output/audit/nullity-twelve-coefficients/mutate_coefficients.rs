use std::{fs, path::Path, process::Command};

fn compile(root: &Path, source: &Path) -> Result<std::process::Output, std::io::Error> {
    Command::new("opam")
        .args([
            "exec",
            "--switch=rocq-9.3",
            "--",
            "rocq",
            "compile",
            "-q",
            "-w",
            "@default",
            "-Q",
        ])
        .arg(root.join("proofs/theories"))
        .arg("OpenGororoba")
        .arg(source)
        .output()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let arguments = std::env::args_os().collect::<Vec<_>>();
    if arguments.len() != 3 {
        return Err("usage: mutate-coefficients CHECKOUT OUTPUT_DIRECTORY".into());
    }
    let root = Path::new(&arguments[1]);
    let destination = Path::new(&arguments[2]);
    fs::create_dir_all(destination)?;
    let original = fs::read_to_string(
        root.join("proofs/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v"),
    )?;
    let cases = [
        ("Control", "", ""),
        (
            "Coefficient",
            "(30%nat,6%nat,(2)%Z)",
            "(30%nat,6%nat,(3)%Z)",
        ),
        (
            "Reconstruction",
            "(30%nat,0%nat,(2)%Z)",
            "(30%nat,0%nat,(3)%Z)",
        ),
        (
            "MonomialOrder",
            "(0%nat,0%nat);(1%nat,1%nat)",
            "(1%nat,1%nat);(0%nat,0%nat)",
        ),
        (
            "GeneratorSign",
            "z 17%nat*z 5%nat-z 13%nat*z 20%nat",
            "z 17%nat*z 5%nat+z 13%nat*z 20%nat",
        ),
    ];
    for (name, before, after) in cases {
        if name != "Control" && !original.contains(before) {
            return Err(format!("mutation anchor absent: {name}").into());
        }
        let mutated = if name == "Control" {
            original.clone()
        } else {
            original.replacen(before, after, 1)
        };
        let source = destination.join(format!("{name}.v"));
        fs::write(&source, mutated)?;
        let output = compile(root, &source)?;
        fs::write(destination.join(format!("{name}.stdout")), &output.stdout)?;
        fs::write(destination.join(format!("{name}.stderr")), &output.stderr)?;
        let expected_success = name == "Control";
        if output.status.success() != expected_success {
            return Err(format!("unexpected compile verdict: {name}; {}", output.status).into());
        }
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !expected_success
            && !(stderr.contains("Unable to unify") || stderr.contains("not a valid ring equation"))
        {
            return Err(format!("unexpected failure mechanism: {name}: {stderr}").into());
        }
        println!(
            "{name}: {}",
            if expected_success {
                "accepted"
            } else {
                "rejected"
            }
        );
    }
    Ok(())
}
