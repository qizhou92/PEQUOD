### Automatic Jave Program Equivalence Verification
 
 1. PEQUOD is a tool, implemented on Java, for the automatic static verification for checking program equivalence between two 
 programs.
 
 2. PEQUOD implemented on [SOOT](https://sable.github.io/soot/) as the intermeida representation for Java program, and [Z3]
 (https://github.com/Z3Prover/z3) as the SMT solver to verify the equivalence propery corss two programs.  

### Examples
 
```java
public int
  addDigits0(int num) {
  int result = num -
    9 * ((num - 1) / 9);
  return result; }
```

```java
public int
  addDigits1(int num) {
  while (num > 9) {
    num = num / 10 +
      num % 10; }
  return num; }
}
```

PEQUOD can verify when num is greater or equal to zero, addDigits0 and addDigits1 produce the same return value.
   
### Reference Paper

Completely Automated Equivalence Proofs
