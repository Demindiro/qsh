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
	pub fn new(s: &'a str) -> Self {
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

		while let Some((i, c)) = self.iter.next() {
			let t = match c {
				'#' => {
					while let Some((_, c)) = self.iter.next() {
						if c == '\n' {
							break;
						}
					}
					f(Token::Separator)
				}
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

	fn cmp(s: &str, t: &[Token]) {
		let s = TokenParser::new(s).map(Result::unwrap).collect::<Vec<_>>();
		assert_eq!(&s, t);
	}

	#[test]
	fn test() {
		let s = "
print beep booop   baap {cat /etc/passwd }

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
}
