use super::{Op, ParseError, Parser};
use crate::runtime::QFunction;

impl<'a, F> Parser<'a, F>
where
	F: (Fn(&str) -> Option<QFunction>) + Clone,
{
	/// Check for any errors. This should only be called *after* [`Self::reduce`]`.
	pub(super) fn validate(&self, ops: &[Op<'a>]) -> Result<(), ParseError> {
		let fns = self.functions.as_ref().unwrap();
		self.validate_inner(ops)?;
		for f in fns.values() {
			self.validate_inner(&f.ops)?;
		}
		Ok(())
	}

	/// Check for any error in a (sub-)tree.
	fn validate_inner(&self, ops: &[Op<'a>]) -> Result<(), ParseError> {
		for op in ops.iter() {
			match op {
				Op::Call {
					function,
					arguments,
					pipe_in,
					pipe_out,
				} => {
					let f = &self.functions.as_ref().unwrap()[function];
					if arguments.len() != f.arguments.len() {
						return Err(ParseError::ArgumentMismatch);
					} else if pipe_in.len() != f.pipe_in.len() {
						return Err(ParseError::PipeInMismatch);
					} else if pipe_out.len() != f.pipe_out.len() {
						return Err(ParseError::PipeOutMismatch);
					}
				}
				Op::If { .. } => {}
				Op::While { .. } => {}
				Op::For { .. } => {}
				Op::Assign { .. } => (),
				Op::Exec { .. } | Op::CallBuiltin { .. } => (),
			}
		}
		Ok(())
	}
}

#[cfg(test)]
mod test {
	use super::super::super::test::*;

	#[test]
	fn too_little_args() {
		assert!(try_parse("fn foo x <y >z; bar; foo <y >z").is_err());
	}

	#[test]
	fn too_many_args() {
		assert!(try_parse("fn foo x <y >z; bar; foo @y @w <y >z").is_err());
	}

	#[test]
	fn too_little_args_2() {
		assert!(try_parse("fn foo x w <y >z; bar; foo @y <y >z").is_err());
	}

	#[test]
	fn recursive_too_little_args() {
		assert!(try_parse("fn foo x w <y >z; foo @y <y >z").is_err());
	}
}
