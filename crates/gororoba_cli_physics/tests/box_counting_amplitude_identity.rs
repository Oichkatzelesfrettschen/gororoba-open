use cosmology_core::sersic::{
    box_counting_fractal_dim, box_counting_fractal_dim_threshold, otsu_threshold,
};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[derive(Debug)]
struct Observation {
    counts: [usize; 4],
    mask: Vec<u8>,
    measured_slope: Option<f64>,
}

fn observe(density: &[f64], threshold: f64) -> Observation {
    assert_eq!(density.len(), 16 * 16 * 16);
    assert!(density.iter().all(|value| value.is_finite()));
    let mask: Vec<_> = density
        .iter()
        .map(|value| u8::from(*value > threshold))
        .collect();
    let counts = [1, 2, 4, 8].map(|scale| {
        let mut occupied = BTreeSet::new();
        for (index, selected) in mask.iter().enumerate() {
            if *selected != 0 {
                occupied.insert((
                    (index % 16) / scale,
                    ((index / 16) % 16) / scale,
                    (index / 256) / scale,
                ));
            }
        }
        occupied.len()
    });
    let measured_slope = if counts.iter().all(|count| *count > 0) {
        Some(
            -counts
                .iter()
                .enumerate()
                .map(|(index, count)| (index as f64 - 1.5) * (*count as f64).ln())
                .sum::<f64>()
                / (5.0 * 2.0_f64.ln()),
        )
    } else {
        None
    };
    Observation {
        counts,
        mask,
        measured_slope,
    }
}

fn record(label: &str, density: &[f64], threshold: f64, observation: &Observation) {
    let minimum = density.iter().copied().fold(f64::INFINITY, f64::min);
    let maximum = density.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    println!(
        "label={label} min={minimum:.17} max={maximum:.17} range={:.17} threshold={threshold:.17} scales=[1,2,4,8] counts={:?} mask_sha256={} measured_slope={:?} scalar={:.17}",
        maximum - minimum,
        observation.counts,
        digest(&observation.mask),
        observation.measured_slope,
        box_counting_fractal_dim_threshold(density, 16, 16, 16, threshold)
    );
}

#[test]
fn exact_plane_affine_controls_preserve_geometry_at_tiny_contrast() {
    for offset in [0.0, 1.0] {
        for amplitude in [1.0, 2.0_f64.powi(-20), 2.0_f64.powi(-40)] {
            let density: Vec<_> = (0..4096)
                .map(|index| offset + if index % 16 == 8 { amplitude } else { 0.0 })
                .collect();
            let threshold = otsu_threshold(&density);
            let observation = observe(&density, threshold);
            assert_eq!(observation.counts, [256, 64, 16, 4]);
            assert!((observation.measured_slope.unwrap() - 2.0).abs() < 1e-12);
            assert!((box_counting_fractal_dim(&density, 16, 16, 16) - 2.0).abs() < 1e-12);
            record(
                &format!("plane_offset{offset}_amplitude{amplitude}"),
                &density,
                threshold,
                &observation,
            );
        }
    }
    let uniform = vec![1.0; 4096];
    let observation = observe(&uniform, otsu_threshold(&uniform));
    assert_eq!(observation.counts, [0; 4]);
    assert!(observation.measured_slope.is_none());
    assert_eq!(box_counting_fractal_dim(&uniform, 16, 16, 16), 3.0);
    record(
        "exact_uniform_no_occupied_convention",
        &uniform,
        1.0,
        &observation,
    );
}
