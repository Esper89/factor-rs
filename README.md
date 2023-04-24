# factor-rs

A command-line program for listing the prime factors of a number or fraction. Uses the
[`prime_factorization`](https://crates.io/crates/prime_factorization) library. Supports all integers
between -2<sup>128</sup> and 2<sup>128</sup>, all fractions (of either sign) with numerator and
denominator below 2<sup>128</sup>, and all decimal numbers (of either sign) with a mantissa below
2<sup>128</sup> and an exponent below 39. Fractions and decimals are also reduced to their lowest
forms.

## Examples

```
$ factor 0 1 3 8 12 -255 4/12 6.125 -7/3 5/0 0/0
0 = 0
1 = 1
3 = 3
8 = 2^3
12 = 2^2 * 3
-255 = -1 * 3 * 5 * 17
4/12 = 3^-1 = 1/3
6.125 = 2^-3 * 7^2 = 49/8
-7/3 = -1 * 3^-1 * 7
5/0 = 5 * 1/0 = 1/0
0/0 = 0/0
```

## License

```
Copyright (c) 2023 Esper Thomson

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
