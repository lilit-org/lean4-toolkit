## basic concepts

<br>

---

### types and functions

<br>

* there are two primary concepts in lean: functions and types
* basic types examples are natural numbers (`Nat`, whole numbers starting from 0), booleans (`Bool`), true or false values, strings
* check types using `#check`
* evaluate expressions using `#eval`

<br>

---

### function definitions

<br>

* functions are defined using the `def` keyword:

```lean
def double (n : Nat) : Nat := n + n
```
