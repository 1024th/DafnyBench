# HumanEval to Dafny

## Categories

I classified the problems of HumanEval dataset into the following categories:

- `impossible_syntax`: the function is impossible to implement in Dafny due to syntax limitations, e.g., the function requires a dynamic type system.
- `spec_body_same`: the body of the function is exactly the same as the specification.
- `story_problem`: the problem is narrative and requires understanding the context to solve, like a [word problem](https://en.wikipedia.org/wiki/Word_problem_(mathematics_education)).
- `paren`: the problem involves parentheses matching, e.g., checking if a string has balanced parentheses.
- `seq`: the problem involves sequences, e.g., sorting, reversing, or finding some elements.
- `string`: the problem involves operations specific to strings, e.g., ASCII code, lowercase, uppercase, vowels, words, or sentences.
- `prime`: the problem involves prime numbers or relevant math concepts.
- `repetitive_arith`: the problem involves repetitive arithmetic operations, which can be solved by looping or recursion, e.g., summing, multiplying, or calculating recursive functions.

## Suitable Problems

Most of the problems in the HumanEval dataset are not suitable for Dafny. Some are just boring chores or strange requirements that are not interesting to verify. Some are too simple and can be solved by a single-line pure function.

But I am still inspired by some problems and think they or their variants might be suitable for Dafny:

- Sequence problems that are easy to specify, e.g., sorting, reversing, or finding some elements.
- String encoding and decoding that can be verified by Dafny.
- Decimal <-> binary conversion, and we can verify the correctness of the conversion.
- Simple number theory problems, e.g., prime number validation or integer factorization. But the proof might be challenging.

I found myself particularly interested in the "conversion" problems, e.g., changing the number base, string encoding and decoding, expression simplification, etc. We can define and verify the correctness of the conversion and prove some properties of the conversion functions.
