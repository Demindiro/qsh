use core::iter::Peekable;
use core::str::CharIndices;

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
	ScopeOpen,
	ScopeClose,
	Word(&'a str),
	String(&'a str),
	Variable(&'a str),
	Integer(isize),
	Pipe {
		from: &'a str,
		to: &'a str,
	},
	PipeOut {
		from: &'a str,
		to: PipeDestination<'a>,
	},
	PipeIn {
		to: &'a str,
		from: PipeDestination<'a>,
	},
	Separator,
}

#[derive(Debug, PartialEq)]
pub enum PipeDestination<'a> {
	Variable(&'a str),
	Stream(&'a str),
}

pub struct TokenParser<'a> {
	/// The string being parsed
	s: &'a str,
	/// The start character of the next token.
	start: usize,
	/// The iterator over the parsed string.
	iter: Peekable<CharIndices<'a>>,
	/// Queue of tokens to be returned.
	queue: Option<Token<'a>>,
	/// Whether the last returned token was a separator
	last_was_separator: bool,
}

#[derive(Debug)]
pub enum TokenError {
	UnclosedScope,
	UnexpectedCloseScope,
	UnterminatedString,
	NoNameVariable,
	NoDigits,
	InvalidDigit,
}

impl<'a> TokenParser<'a> {
	/// Convert a string to a series of tokens
	fn new(s: &'a str) -> Self {
		Self {
			s,
			start: 0,
			iter: s.char_indices().peekable(),
			queue: None,
			last_was_separator: true, // Filter redundant separators at the start
		}
	}
}

impl<'a> Iterator for TokenParser<'a> {
	type Item = Result<Token<'a>, TokenError>;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(t) = self.queue.take() {
			self.last_was_separator = t == Token::Separator;
			return Some(Ok(t));
		}

		let f = |t| {
			fn parse_pipe(p: &str) -> PipeDestination {
				match p {
					p if p.starts_with("@") => PipeDestination::Variable(&p[1..]),
					p => PipeDestination::Stream(p),
				}
			}
			match t {
				Token::Word(s) if s == "" => None,
				Token::Separator if self.last_was_separator => None,
				Token::Word(s) if let Some((from, to)) = s.split_once('|') => {
					Some(Token::Pipe { from, to })
				}
				Token::Word(s) if let Some((from, to)) = s.split_once('>') => {
					Some(Token::PipeOut { from, to: parse_pipe(to) })
				}
				Token::Word(s) if let Some((from, to)) = s.split_once('<') => {
					Some(Token::PipeIn { to, from: parse_pipe(from) })
				}
				Token::Word(s) if s.chars().next() == Some('@') => Some(Token::Variable(&s[1..])),
				t => Some(t),
			}
		};

		while let Some((i, c)) = self.iter.next() {
			let t = match c {
				';' | '\n' => {
					let a = f(Token::Word(&self.s[self.start..i]));
					let b = f(Token::Separator);
					if a.is_some() && b.is_some() {
						self.queue = b;
						a
					} else {
						a.or(b)
					}
				}
				' ' | '\t' => f(Token::Word(&self.s[self.start..i])),
				'{' => f(Token::ScopeOpen),
				'}' => f(Token::ScopeClose),
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
						Some(n) => f(Token::Integer(n)),
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
					f(Token::String(&self.s[i + 1..j]))
				}
				_ => continue,
			};
			self.start = self.iter.peek().unwrap_or(&(self.s.len(), ' ')).0;
			if let Some(t) = t {
				self.last_was_separator = t == Token::Separator;
				return Some(Ok(t));
			}
		}
		let t = f(Token::Word(&self.s[self.start..]));
		self.start = self.s.len();
		t.map(Ok)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test() {
		let s = "
print beep booop   baap {cat /etc/passwd }

print quack

@a = $5; print @a

ls 1>@ls

ls 2>@error 1| sort -h

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
			Token::ScopeOpen,
			Token::Word("cat"),
			Token::Word("/etc/passwd"),
			Token::ScopeClose,
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
				from: "1",
				to: PipeDestination::Variable("ls"),
			},
			Token::Separator,
			Token::Word("ls"),
			Token::PipeOut {
				from: "2",
				to: PipeDestination::Variable("error"),
			},
			Token::Pipe { from: "1", to: "" },
			Token::Word("sort"),
			Token::Word("-h"),
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
		assert_eq!(
			TokenParser::new(s).map(Result::unwrap).collect::<Vec<_>>(),
			&t
		);
	}
}
