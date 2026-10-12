// SPDX-License-Identifier: GPL-2.0-or-later

//! Exact average/detail coordinates preserve both halves of a doubling.
//!
//! The scalar multiplication witness in `FoldAverageDescent` excludes a
//! product law on averages alone. Retaining the detail channel gives an
//! invertible coordinate change with the original scalar-coordinate count.

use num_rational::BigRational;
use num_traits::Zero;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FoldCoordinateError {
    InvalidDimension(usize),
    MismatchedChannels {
        average_count: usize,
        detail_count: usize,
    },
    InvalidRational,
}

impl std::fmt::Display for FoldCoordinateError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FoldCoordinateError {}

/// A complete coordinate change; the detail channel retains the lost fiber.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AverageDetailCoordinates {
    averages: Vec<BigRational>,
    details: Vec<BigRational>,
}

fn validate_rationals(values: &[BigRational]) -> Result<(), FoldCoordinateError> {
    if values.iter().any(|value| value.denom().is_zero()) {
        return Err(FoldCoordinateError::InvalidRational);
    }
    Ok(())
}

impl AverageDetailCoordinates {
    pub fn from_channels(
        averages: Vec<BigRational>,
        details: Vec<BigRational>,
    ) -> Result<Self, FoldCoordinateError> {
        if averages.len() != details.len() {
            return Err(FoldCoordinateError::MismatchedChannels {
                average_count: averages.len(),
                detail_count: details.len(),
            });
        }
        if !averages.len().is_power_of_two() || averages.len().checked_mul(2).is_none() {
            return Err(FoldCoordinateError::InvalidDimension(averages.len()));
        }
        validate_rationals(&averages)?;
        validate_rationals(&details)?;
        Ok(Self { averages, details })
    }

    pub fn averages(&self) -> &[BigRational] {
        &self.averages
    }

    pub fn details(&self) -> &[BigRational] {
        &self.details
    }

    /// Restore the first half as average+detail and the second as average-detail.
    pub fn reconstruct(&self) -> Vec<BigRational> {
        self.averages
            .iter()
            .zip(&self.details)
            .map(|(average, detail)| average + detail)
            .chain(
                self.averages
                    .iter()
                    .zip(&self.details)
                    .map(|(average, detail)| average - detail),
            )
            .collect()
    }
}

/// Split a positive power-of-two vector of dimension at least two into two channels.
pub fn fold_coordinates_exact(
    coordinates: &[BigRational],
) -> Result<AverageDetailCoordinates, FoldCoordinateError> {
    if coordinates.len() < 2 || !coordinates.len().is_power_of_two() {
        return Err(FoldCoordinateError::InvalidDimension(coordinates.len()));
    }
    validate_rationals(coordinates)?;
    let (first_half, second_half) = coordinates.split_at(coordinates.len() / 2);
    let divisor = BigRational::from_integer(2.into());
    let averages = first_half
        .iter()
        .zip(second_half)
        .map(|(first, second)| (first + second) / &divisor)
        .collect();
    let details = first_half
        .iter()
        .zip(second_half)
        .map(|(first, second)| (first - second) / &divisor)
        .collect();
    Ok(AverageDetailCoordinates { averages, details })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_annihilator::{MultiplicationSide, multiplication_matrix_exact};

    fn rational(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(numerator.into(), denominator.into())
    }

    #[test]
    fn fold_coordinates_round_trip_through_dimension_65536() {
        for dimension in [2, 4, 8, 16, 32, 64, 128, 256, 1024, 4096, 65536] {
            let coordinates: Vec<_> = (0..dimension)
                .map(|coordinate| {
                    rational((coordinate % 29) as i64 - 14, (coordinate % 7) as i64 + 1)
                })
                .collect();
            let folded = fold_coordinates_exact(&coordinates).unwrap();
            assert_eq!(folded.averages().len() + folded.details().len(), dimension);
            assert_eq!(folded.reconstruct(), coordinates);
            let reconstructed_channels = AverageDetailCoordinates::from_channels(
                folded.averages().to_vec(),
                folded.details().to_vec(),
            )
            .unwrap();
            assert_eq!(folded, reconstructed_channels);
        }
    }

    #[test]
    fn equal_averages_acquire_distinct_product_averages() {
        let zero = vec![rational(0, 1), rational(0, 1)];
        let kernel_witness = vec![rational(1, 1), rational(-1, 1)];
        assert_eq!(
            fold_coordinates_exact(&zero).unwrap().averages(),
            fold_coordinates_exact(&kernel_witness).unwrap().averages()
        );
        let products = [&zero, &kernel_witness].map(|coordinates| {
            multiplication_matrix_exact(coordinates, MultiplicationSide::Left)
                .unwrap()
                .column(1)
                .iter()
                .cloned()
                .collect::<Vec<_>>()
        });
        assert_eq!(
            fold_coordinates_exact(&products[0]).unwrap().averages(),
            &[rational(0, 1)]
        );
        assert_eq!(
            fold_coordinates_exact(&products[1]).unwrap().averages(),
            &[rational(1, 1)]
        );
    }

    #[test]
    fn missing_detail_changes_the_original_vector() {
        let coordinates = vec![rational(3, 2), rational(-5, 3)];
        let complete = fold_coordinates_exact(&coordinates).unwrap();
        let damaged = AverageDetailCoordinates::from_channels(
            complete.averages().to_vec(),
            vec![rational(0, 1)],
        )
        .unwrap();
        assert_ne!(damaged.reconstruct(), coordinates);
    }

    #[test]
    fn invalid_domains_fail_before_arithmetic() {
        for dimension in [0, 1, 3] {
            assert_eq!(
                fold_coordinates_exact(&vec![rational(0, 1); dimension]),
                Err(FoldCoordinateError::InvalidDimension(dimension))
            );
        }
        let malformed = BigRational::new_raw(1.into(), 0.into());
        assert_eq!(
            fold_coordinates_exact(&[malformed.clone(), rational(0, 1)]),
            Err(FoldCoordinateError::InvalidRational)
        );
        assert_eq!(
            AverageDetailCoordinates::from_channels(vec![malformed], vec![rational(0, 1)]),
            Err(FoldCoordinateError::InvalidRational)
        );
        assert!(matches!(
            AverageDetailCoordinates::from_channels(vec![rational(0, 1)], vec![]),
            Err(FoldCoordinateError::MismatchedChannels { .. })
        ));
        assert_eq!(
            AverageDetailCoordinates::from_channels(vec![], vec![]),
            Err(FoldCoordinateError::InvalidDimension(0))
        );
    }
}
