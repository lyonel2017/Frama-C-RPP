#  Frama-C-RPP

This is the *RPP (Relational Property Prover)* plug-in of *Frama-C*.

## Relational Properties

Relational properties are properties invoking any finite number of function calls
of possibly dissimilar functions with possible nested calls. Examples:

      ∀ x1,x2; x1 < x2 ⇒ f(x1) < f(x2)

      ∀ message, key; message = Decrypt(Encrypt(message,key),key)

      ∀ x1,x2; compare(x1,x2) == -compare(x2,x1);

      ∀ x1,x2,x3; (compare(x1,x2) > 0 && compare(x2,x3) > 0) ==> compare(x1,x3) > 0;

      ∀ x1,x2,x3; compare(x1,x2) == 0 ==> compare(x1,x3) == compare(x2,x3);


## A Relational Property Prover

*RPP* is a *Frama-C* plug-in designed for the proof of relational properties.
It is based on the technique of self-composition and works like a preprocessor
for *WP* plug-in. After its execution on a project containing relational
properties annotations, the proof on the generated code proceeds like any other
proof with *WP*: proof obligations are generated and can be either discharged
automatically by automatic theorem
provers (e.g. *Alt-Ergo*, *CVC4*, *Z3*) or proven interactively (e.g. in *Coq*).
The plug-in also generates an axiomatic definition and additional annotations
that allow to use a relational property as a hypothesis for the proof of
other properties in a completely automatic and transparent way.

## Installation

*RPP v0.0.1* requires [Frama-C v24.0 Chromium](https://frama-c.com/fc-versions/chromium.html).
For more information see [Frama-C](http://frama-c.com).

For installation, run following commands in the *RPP* directory:

        make
        make install

## Usage

- For command ligne interface:

            frama-c -rpp file.c

- For graphic user interface (call from terminal):

            frama-c-gui -rpp file.c

- For graphic user interface (call from gui): select a relational clause in the gui,
right click and select *RPP*. A new project will be generated ("RPP proof system").

- For generating only the self-composition transformation:

           frama-c -rpp -rpp-pro file.c

- For generating only the acsl annotations:

           frama-c -rpp -rpp-hyp file.c

## Example of relational properties specification

Concider function *f*:

```c
        int f(int x){
            return x + 1;
        }
```

If we want to specify monotony on function *f* we can write:

```c
        int f(int x){
            return x + 1;
        }

        /*@ relational \forall int x1,x2; \callset(\call(f,x1,id1),\call(f,x2,id2)),
                                          x1 < x2 ==> \callresult(id1) < \callresult(id2);*/
```

Or, because *f* has no side effect, we can also write a shorter form for pure functions:

```c
        int f(int x){
            return x + 1;
        }

        /*@ relational \forall int x1,x2 ; x1 < x2 ==> \callpure(f,x1) < \callpure(f,x2);*/
```

If we now consider function *g* and global variable *y*:

```c
        int y;

        int g(){
            y = y + 1;
        }
```

The specification of monotony on *g* can be written as follows:

```c
        int y;

        int g(){
            y = y + 1;
        }

        /*@ relational \callset(\call(f,id1),\call(f,id2)),
                       \at(y,Pre_id1) < \at(y,Pre_id2) ==> \at(y,Post_id1) < \at(y,Post_id2);*/
```

More examples are available in :

        test/rpp/
        benchmarks/stackoverflow

More documentations can be found in:

         doc/
