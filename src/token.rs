use core::iter::Peekable;
use core::mem;
use core::str::CharIndices;

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
	BlockOpen,
	BlockClose,
	Word(&'a str),
	String(&'a str),
	Variable(&'a str),
	Integer(isize),
	PipeOut { from: &'a str, to: &'a str },
	PipeIn { to: &'a str, from: &'a str },
	Separator,
}

pub struct TokenParser<'a> {
	/// The string being parsed
	s: &'a str,
	/// The start character of the next token.
	start: usize,
	/// The iterator over the parsed string.
	iter: Peekable<CharIndices<'a>>,
	/// Queue of tokens to be returned.
	queue: Queue<'a>,
	/// Whether the last returned token was a separator
	last_was_separator: bool,
}

#[derive(Debug)]
pub enum TokenError {
	UnclosedBlock,
	UnexpectedCloseBlock,
	UnterminatedString,
	NoNameVariable,
	NoDigits,
	InvalidDigit,
}

/// A queue of tokens to be returned
enum Queue<'a> {
	None,
	One(Token<'a>),
	Two(Token<'a>, Token<'a>),
	Three(Token<'a>, Token<'a>, Token<'a>),
}

impl<'a> Queue<'a> {
	/// Pop an item from the queue.
	fn pop(&mut self) -> Option<Token<'a>> {
		let t;
		(*self, t) = match mem::replace(self, Self::None) {
			Self::None => (Self::None, None),
			Self::One(t) => (Self::None, Some(t)),
			Self::Two(t, u) => (Self::One(u), Some(t)),
			Self::Three(t, u, v) => (Self::Two(u, v), Some(t)),
		};
		t
	}

	/// Enqueue an array of tokens.
	///
	/// # Panics
	///
	/// The queue isn't empty.
	///
	/// There are more items than the queue can hold.
	fn push<const N: usize>(&mut self, mut tokens: [Token<'a>; N]) {
		if let Self::None = self {
			let mut f = |i| mem::replace(&mut tokens[i], Token::Separator);
			*self = match N {
				0 => Self::None,
				1 => Self::One(f(0)),
				2 => Self::Two(f(0), f(1)),
				3 => Self::Three(f(0), f(1), f(2)),
				_ => panic!("more items than the queue can hold"),
			};
		} else {
			panic!("the queue isn't empty");
		}
	}
}

impl<'a> TokenParser<'a> {
	/// Convert a string to a series of tokens
	pub fn new(s: &'a str) -> Self {
		Self {
			s,
			start: 0,
			iter: s.char_indices().peekable(),
			queue: Queue::None,
			last_was_separator: true, // Filter redundant separators at the start
		}
	}

	/// Try to pop & transform a token from the queue.
	fn pop(&mut self) -> Option<Token<'a>> {
		let f = |t| {
			match t {
				Token::Word(s) if s == "" => None,
				Token::Separator if self.last_was_separator => None,
				Token::Word(s) if let Some((from, to)) = s.split_once('>') => {
					Some(Token::PipeOut { from, to })
				}
				Token::Word(s) if let Some((to, from)) = s.split_once('<') => {
					Some(Token::PipeIn { to, from })
				}
				Token::Word(s) if s.chars().next() == Some('@') => Some(Token::Variable(&s[1..])),
				t => Some(t),
			}
		};

		while let Some(t) = self.queue.pop() {
			if let Some(t) = f(t) {
				self.last_was_separator = t == Token::Separator;
				return Some(t);
			}
		}

		None
	}

	/// Enqueue an array of tokens.
	///
	/// # Panics
	///
	/// See [`Queue::push`].
	fn push<const N: usize>(&mut self, tokens: [Token<'a>; N]) {
		self.queue.push(tokens)
	}
}

impl<'a> Iterator for TokenParser<'a> {
	type Item = Result<Token<'a>, TokenError>;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(t) = self.pop() {
			return Some(Ok(t));
		}

		while let Some((i, c)) = self.iter.next() {
			let () = match c {
				'#' => {
					while let Some((_, c)) = self.iter.next() {
						if c == '\n' {
							break;
						}
					}
					self.push([Token::Separator]);
				}
				';' | '\n' => self.push([Token::Word(&self.s[self.start..i]), Token::Separator]),
				' ' | '\t' => self.push([Token::Word(&self.s[self.start..i])]),
				'(' => self.push([Token::Word(&self.s[self.start..i]), Token::BlockOpen]),
				')' => {
					// Put a separator before the block close to simplify things.
					self.push([
						Token::Word(&self.s[self.start..i]),
						Token::Separator,
						Token::BlockClose,
					])
				}
				'$' => {
					let (radix, skip) = match self.iter.peek() {
						Some((_, 'b')) => (2, true),
						Some((_, 'o')) => (8, true),
						Some((_, 'x')) => (16, true),
						Some(&(_, c)) if '0' <= c && c <= '9' => (10, false),
						Some(_) => return Some(Err(TokenError::InvalidDigit)),
						None => return Some(Err(TokenError::NoDigits)),
					};
					skip.then(|| self.iter.next());
					let mut n = None;
					loop {
						n = match self.iter.peek() {
							Some((_, c)) if " ;".contains(|e| e == *c) => break,
							Some((_, c)) => match c.to_digit(radix) {
								Some(d) => {
									self.iter.next();
									Some(n.unwrap_or(0) * 10 + isize::try_from(d).unwrap())
								}
								None => return Some(Err(TokenError::InvalidDigit)),
							},
							_ => return Some(Err(TokenError::InvalidDigit)),
						};
					}
					match n {
						Some(n) => self.push([Token::Integer(n)]),
						None => return Some(Err(TokenError::NoDigits)),
					}
				}
				'"' => {
					let mut j = i;
					while let Some((k, c)) = self.iter.next() {
						j = k;
						match c {
							'"' => break,
							'\\' => todo!("string escape"),
							_ => (),
						}
					}
					self.push([Token::String(&self.s[i + 1..j])]);
				}
				_ => continue,
			};
			self.start = self.iter.peek().unwrap_or(&(self.s.len(), ' ')).0;

			if let Some(t) = self.pop() {
				return Some(Ok(t));
			}
		}

		// We're at the end of the source file.
		self.push([Token::Word(&self.s[self.start..])]);
		if let Some(t) = self.pop() {
			self.start = self.s.len();
			Some(Ok(t))
		} else if !self.last_was_separator {
			// Always end with a separator to simplify things.
			self.last_was_separator = true;
			Some(Ok(Token::Separator))
		} else {
			None
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;

	fn cmp(s: &str, t: &[Token]) {
		let s = TokenParser::new(s).map(Result::unwrap).collect::<Vec<_>>();
		assert_eq!(&s, t);
	}

	#[test]
	fn test() {
		let s = "
print beep booop   baap (cat /etc/passwd)

print quack

@a = $5; print @a

ls 2>error 1>
sort -h 0<

if @error == ping
	print \"p  o  n  g\"

if @error != \"\"
	print Error: @error
";
		let t = [
			Token::Word("print"),
			Token::Word("beep"),
			Token::Word("booop"),
			Token::Word("baap"),
			Token::BlockOpen,
			Token::Word("cat"),
			Token::Word("/etc/passwd"),
			Token::Separator,
			Token::BlockClose,
			Token::Separator,
			Token::Word("print"),
			Token::Word("quack"),
			Token::Separator,
			Token::Variable("a"),
			Token::Word("="),
			Token::Integer(5),
			Token::Separator,
			Token::Word("print"),
			Token::Variable("a"),
			Token::Separator,
			Token::Word("ls"),
			Token::PipeOut {
				from: "2",
				to: "error",
			},
			Token::PipeOut { from: "1", to: "" },
			Token::Separator,
			Token::Word("sort"),
			Token::Word("-h"),
			Token::PipeIn { from: "", to: "0" },
			Token::Separator,
			Token::Word("if"),
			Token::Variable("error"),
			Token::Word("=="),
			Token::Word("ping"),
			Token::Separator,
			Token::Word("print"),
			Token::String("p  o  n  g"),
			Token::Separator,
			Token::Word("if"),
			Token::Variable("error"),
			Token::Word("!="),
			Token::String(""),
			Token::Separator,
			Token::Word("print"),
			Token::Word("Error:"),
			Token::Variable("error"),
			Token::Separator,
		];
		cmp(s, &t);
	}

	#[test]
	fn comment() {
		let s = "
# Ignore me; print oh no

print \"Don't ignore me!\" # Do ignore this though
";
		let t = [
			Token::Word("print"),
			Token::String("Don't ignore me!"),
			Token::Separator,
		];
		cmp(s, &t);
	}

	#[test]
	fn block() {
		let s = "(cat a)";
		let t = [
			Token::BlockOpen,
			Token::Word("cat"),
			Token::Word("a"),
			Token::Separator,
			Token::BlockClose,
			Token::Separator,
		];
		cmp(s, &t);
	}
}
