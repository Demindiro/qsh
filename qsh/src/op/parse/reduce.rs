use super::{Expression, Op, Parser};
use crate::runtime::QFunction;
use core::mem;

impl<'a, F> Parser<'a, F>
where
	F: (Fn(&str) -> Option<QFunction>) + Clone,
{
	/// Simplify the [`Op`] tree by removing redundant operations & transforming calls
	/// to built-in, user-defined functions or external programs
	pub(super) fn reduce(&mut self, mut ops: Box<[Op<'a>]>) -> Box<[Op<'a>]> {
		for op in ops.iter_mut() {
			match op {
				Op::Call {
					function,
					arguments,
					pipe_in,
					pipe_out,
				} => {
					// Always resolve built-in functions first.
					if let Some(f) = (self.resolve_fn)(function) {
						*op = Op::CallBuiltin {
							function: f,
							arguments: mem::take(arguments),
							pipe_in: mem::take(pipe_in),
							pipe_out: mem::take(pipe_out),
						};
					// Try to resolve user-defined function ...
					} else if self
						.functions
						.as_ref()
						.map_or(false, |f| f.contains_key(function))
					{
						// ... and do nothing
						// Otherwise it's probably an external program.
					} else {
						*op = Op::Exec {
							arguments: Some(Expression::String((&**function).into()))
								.into_iter()
								.chain(mem::take(arguments).into_vec())
								.collect(),
							pipe_in: mem::take(pipe_in),
							pipe_out: mem::take(pipe_out),
						}
					}
				}
				Op::If {
					condition,
					if_true,
					if_false,
				} => {
					if let Expression::Statement(ref mut c) = condition {
						*c = self.reduce(mem::take(c));
					}
					*if_true = self.reduce(mem::take(if_true));
					*if_false = self.reduce(mem::take(if_false));
				}
				Op::While {
					condition,
					while_true,
				} => {
					if let Expression::Statement(ref mut c) = condition {
						*c = self.reduce(mem::take(c));
					}
					*while_true = self.reduce(mem::take(while_true));
				}
				Op::For { for_each, .. } => {
					*for_each = self.reduce(mem::take(for_each));
				}
				Op::Assign { .. } => (),
				Op::Exec { .. } | Op::CallBuiltin { .. } => (),
			}
		}
		ops
	}
}
