# Quack Shell

## Goals

- Concise syntax for executing functions & programs
- Easy to define *and save* functions & variables (REPL-esque)
- Make accidental security exploits hard (see `bash`)

## Example

```qsh
#!/usr/bin/env qsh

print Files in directory:

@INDENT = "  "
for file in (split (ls 1>@) sep="\n") (
	print @INDENT file sep=""
)

fn random
	4

fn rand_either a b (
	if (random) % 2 == 0
		@a
	else
		@b
)

print random                    # Prints "random"
print (random)                # Calls the random function and prints the return value
print (rand_either foo bar)   # Prints either "foo" or "bar"

print 0000    # Prints 0000
print $0000   # Prints 0
print $xff   # Prints 255

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
