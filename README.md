# Quack Shell

## Goals

- Concise syntax for executing functions & programs
- Easy to define *and save* functions & variables (REPL-esque)
- Make accidental security exploits hard (see `bash`)
- Efficient piping of data between processes

## Example

```qsh
#!/usr/bin/env qsh

print Files in directory:

ls 1>ls
split 0<ls 1>ls sep<"\n"
for file in @ls (
	print "  " @file sep=""
)

fn random
	@ = 4

fn rand_either a b (
	if (random) % 2 == 0
		@ = @a
	else
		@ = @b
)

print random                      # Prints "random"
random >; print @                 # Calls the random function and prints the return value
rand_either foo bar >; print @    # Prints either "foo" or "bar"

print 0000    # Prints 0000
print $0000   # Prints 0
print $xff    # Prints 255

@list = [$1, bar]
@map = {foo: $2}
```

## Specification

- Separators: `;`, `\n`
- Scope: `{ a; b; ...; ret }`
  - A scope counts as a single statement
  - The last value (`ret`) is returned
  - Exiting early is possible with `return`
- Variables: `@x = 5`, `print @x`
- Whitespace outside quotes is ignored.


### Types

- Strings
- Integers
- Pipes
- Arrays
- Dictionaries


### Functions

All functions return an integer status code. Other return values can be
extracted using pipes.
