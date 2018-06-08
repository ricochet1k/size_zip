use std::ops::{Add, Sub};

pub fn size_zip<A, B, S, SA, SB>(
    left: A,
    right: B,
    left_size: SA,
    right_size: SB,
) -> SizeZip<<A as IntoIterator>::IntoIter, <B as IntoIterator>::IntoIter, S, SA, SB>
where
    A: IntoIterator,
    B: IntoIterator,
    S: Add<S, Output = S> + Sub<S, Output = S> + PartialOrd + Copy,
    SA: Fn(<<A as IntoIterator>::IntoIter as Iterator>::Item) -> S + Sized,
    SB: Fn(<<B as IntoIterator>::IntoIter as Iterator>::Item) -> S + Sized,
{
    SizeZip {
        left: left.into_iter(),
        right: right.into_iter(),
        left_size,
        right_size,
        saved: Neither,
    }
}

#[derive(Debug)]
enum MaybeEither<L, R> {
    Neither,
    Left(L),
    Right(R),
}
use MaybeEither::*;

pub struct SizeZip<A, B, S, SA, SB>
where
    A: Iterator,
    B: Iterator,
    S: Add<S, Output = S> + Sub<S, Output = S> + PartialOrd + Copy,
    SA: Fn(A::Item) -> S + Sized,
    SB: Fn(B::Item) -> S + Sized,
{
    left: A,
    right: B,
    left_size: SA,
    right_size: SB,
    saved: MaybeEither<WithRange<A::Item, S>, WithRange<B::Item, S>>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct WithRange<A, S> {
    val: A,
    start: S,
    size: S,
}

impl<A, B, S, SA, SB> Iterator for SizeZip<A, B, S, SA, SB>
where
    A: Iterator,
    <A as Iterator>::Item: Copy,
    <B as Iterator>::Item: Copy,
    B: Iterator,
    S: Add<S, Output = S> + Sub<S, Output = S> + PartialOrd + Copy,
    SA: Fn(A::Item) -> S + Sized,
    SB: Fn(B::Item) -> S + Sized,
{
    type Item = (Option<WithRange<A::Item, S>>, Option<WithRange<B::Item, S>>);

    #[cfg_attr(feature = "cargo-clippy", allow(eq_op))]
    fn next(&mut self) -> Option<Self::Item> {
        let mut saved = Neither;
        std::mem::swap(&mut saved, &mut self.saved);
        let (left, right) = match saved {
            Neither => (None, None),
            Left(l) => (Some(l), None),
            Right(r) => (None, Some(r)),
        };
        // use the saved value if there is one, otherwise load a new one from the iterator
        let left = left.map_or_else(
            || {
                self.left.next().map(|i| {
                    let s = (self.left_size)(i);
                    WithRange {
                        val: i,
                        start: s - s,
                        size: s,
                    }
                })
            },
            Some,
        );
        let right = right.map_or_else(
            || {
                self.right.next().map(|i| {
                    let s = (self.right_size)(i);
                    WithRange {
                        val: i,
                        start: s - s,
                        size: s,
                    }
                })
            },
            Some,
        );
        match (left, right) {
            (None, None) => None,
            (Some(l), None) => Some((Some(l), None)),
            (None, Some(r)) => Some((None, Some(r))),
            (Some(l), Some(r)) => {
                if l.size == r.size {
                    Some((Some(l), Some(r)))
                } else if l.size < r.size {
                    self.saved = Right(WithRange {
                        val: r.val,
                        start: r.start + l.size,
                        size: r.size - l.size,
                    });
                    Some((
                        Some(l),
                        Some(WithRange {
                            val: r.val,
                            start: r.start,
                            size: l.size,
                        }),
                    ))
                } else {
                    self.saved = Left(WithRange {
                        val: l.val,
                        start: l.start + r.size,
                        size: l.size - r.size,
                    });
                    Some((
                        Some(WithRange {
                            val: l.val,
                            start: l.start,
                            size: r.size,
                        }),
                        Some(r),
                    ))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        // no items each
        assert_eq!(
            size_zip(&[] as &[u32], &[] as &[u32], |_a| 1, |_b| 1).collect::<Vec<_>>(),
            vec![]
        );

        // one item left
        assert_eq!(
            size_zip(&[1], &[], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![(
                Some(WithRange {
                    val: &1,
                    start: 0,
                    size: 1,
                }),
                None,
            )]
        );

        // one item right
        assert_eq!(
            size_zip(&[], &[1], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![(
                None,
                Some(WithRange {
                    val: &1,
                    start: 0,
                    size: 1,
                }),
            )]
        );

        // one item each
        assert_eq!(
            size_zip(&[1], &[1], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![(
                Some(WithRange {
                    val: &1,
                    start: 0,
                    size: 1,
                }),
                Some(WithRange {
                    val: &1,
                    start: 0,
                    size: 1,
                }),
            )]
        );

        // left more items than right
        assert_eq!(
            size_zip(&[1, 2], &[1], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![
                (
                    Some(WithRange {
                        val: &1,
                        start: 0,
                        size: 1,
                    }),
                    Some(WithRange {
                        val: &1,
                        start: 0,
                        size: 1,
                    }),
                ),
                (
                    Some(WithRange {
                        val: &2,
                        start: 0,
                        size: 2,
                    }),
                    None,
                ),
            ]
        );

        // right more items than left
        assert_eq!(
            size_zip(&[1, 2], &[1], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![
                (
                    Some(WithRange {
                        val: &1,
                        start: 0,
                        size: 1,
                    }),
                    Some(WithRange {
                        val: &1,
                        start: 0,
                        size: 1,
                    }),
                ),
                (
                    Some(WithRange {
                        val: &2,
                        start: 0,
                        size: 2,
                    }),
                    None,
                ),
            ]
        );

        // different sizes
        assert_eq!(
            size_zip(&[1, 2, 3], &[2, 4], |a| *a, |b| *b).collect::<Vec<_>>(),
            vec![
                (
                    Some(WithRange {
                        val: &1,
                        start: 0,
                        size: 1,
                    }),
                    Some(WithRange {
                        val: &2,
                        start: 0,
                        size: 1,
                    }),
                ),
                (
                    Some(WithRange {
                        val: &2,
                        start: 0,
                        size: 1,
                    }),
                    Some(WithRange {
                        val: &2,
                        start: 1,
                        size: 1,
                    }),
                ),
                (
                    Some(WithRange {
                        val: &2,
                        start: 1,
                        size: 1,
                    }),
                    Some(WithRange {
                        val: &4,
                        start: 0,
                        size: 1,
                    }),
                ),
                (
                    Some(WithRange {
                        val: &3,
                        start: 0,
                        size: 3,
                    }),
                    Some(WithRange {
                        val: &4,
                        start: 1,
                        size: 3,
                    }),
                ),
            ]
        );
    }
}
