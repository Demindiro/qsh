# Quack Shell

## Goals

- Concise & simple syntax for executing functions & programs
- Easy to define *and save* functions & variables (REPL-esque)
- Make accidental security vulnerabilities hard (see `bash`)
- Efficient piping of data between processes

## Example

```qsh
#!/usr/bin/env qsh

print Files in directory:

ls >
split < >
print @
for file in @; (
	file @file >type
	if @file; print ">" @file is @type
)

fn random >
	@ = $4

fn rand_either a b >r; (
	random >
	expr @ % 2 >
	printf %c @ >
	@r = @a
	if test @ -eq 1
		@r = @b
)

print random                      # Prints "random"
random >; print @                 # Calls the random function and prints the return value
rand_either foo bar r>; print @   # Prints either "foo" or "bar"

print 0000    # Prints 0000
print $0000   # Prints 0
print $xff    # Prints 255
```

## Specification

**Note:** This specification is not yet complete and is subject to change.
The shell does not implement all features yet either.

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
- Dictionaries (TODO)


### Functions

All functions return an integer status code. Other return values can be
extracted using pipes.


### Streams

**Note:** none of this is implemented. Output is collected into a string.

The main mechanism for exchanging data with programs are streams: data is
continuously written and read from a stream.

in `qsh`, streams and strings are identical from an abstract viewpoint. In
practice they have different performance characteristics: while strings are
stored entirely in memory, streams instead only buffer a portion of data at
any time. This makes them ideal for exchanging a large amount of data.

Estabilishing a stream from one program to another is done through pipes.
Each pipe has exactly one input and one output, i.e.:

```qsh
# This is fine
read a.txt 1>
write b.txt 1<

# The stream from `read a.txt` is lost
read a.txt 1>
read b.txt 1>

# `write b.txt` will not write any data since `write a.txt` wrote all of it
write a.txt 1<
write b.txt 1<
```

A newly created pipe always has its input attached. If the input becomes
disconnected, the pipe becomes unusable.


### Special variables

To keep scripts short, some variables automatically get a value assigned.
These variables cannot be assigned to directly.

- `@?`: the return value of a call.
