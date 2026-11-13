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
        proof_root.join("checkpoints/schur-geometry/CDUnconditionalDoublingNullity.v"),
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
    if !compile("UnalteredDoubling", &source)? {
        return Err("unaltered doubling file failed; mutation rejection is inconclusive".into());
    }
    // Each nullity mutation drops one summand of a doubled nullity, a false claim at the zero
    // operand, where every nullity equals the full dimension. The rank mutation equates rank R_a
    // with rank L_0 = 0, a false claim at the real unit, whose operators have full rank. The
    // harness checks that the unchanged proof script no longer closes the altered statement; it
    // does not instantiate those counterexamples.
    let mutations = [
        (
            "LeftDoublingSingleNullity",
            "Theorem doubling_nullity order operand :\n tower_left_nullity (S order) (operand,tower_zero order) =\n ssrnat.addn (tower_left_nullity order operand) (tower_left_nullity order operand).",
            "Theorem doubling_nullity order operand :\n tower_left_nullity (S order) (operand,tower_zero order) =\n tower_left_nullity order operand.",
        ),
        (
            "RightDoublingSingleNullity",
            "Theorem right_doubling_nullity order operand :\n tower_right_nullity (S order) (operand,tower_zero order) =\n ssrnat.addn (tower_right_nullity order operand) (tower_right_nullity order operand).",
            "Theorem right_doubling_nullity order operand :\n tower_right_nullity (S order) (operand,tower_zero order) =\n tower_right_nullity order operand.",
        ),
        (
            "ZeroLowerHalfSingleNullity",
            "Theorem zero_lower_half_nullity order operand :\n tower_left_nullity (S order) (tower_zero order,operand) =\n ssrnat.addn (tower_left_nullity order operand) (tower_left_nullity order operand).",
            "Theorem zero_lower_half_nullity order operand :\n tower_left_nullity (S order) (tower_zero order,operand) =\n tower_left_nullity order operand.",
        ),
        (
            "ZeroLowerHalfRightSingleNullity",
            "Theorem zero_lower_half_right_nullity order operand :\n tower_right_nullity (S order) (tower_zero order,operand) =\n ssrnat.addn (tower_right_nullity order operand) (tower_right_nullity order operand).",
            "Theorem zero_lower_half_right_nullity order operand :\n tower_right_nullity (S order) (tower_zero order,operand) =\n tower_right_nullity order operand.",
        ),
        (
            "RightLeftRankAgainstZero",
            "Theorem tower_right_left_rank order operand :\n mxrank (tower_right_matrix order operand) = mxrank (tower_left_matrix order operand).",
            "Theorem tower_right_left_rank order operand :\n mxrank (tower_right_matrix order operand) = mxrank (tower_left_matrix order (tower_zero order)).",
        ),
    ];
    for (name, before, after) in mutations {
        if source.matches(before).count() != 1 {
            return Err(format!("mutation anchor must occur exactly once: {name}").into());
        }
        if compile(name, &source.replacen(before, after, 1))? {
            return Err(format!("altered law accepted: {name}").into());
        }
    }
    Ok(())
}
