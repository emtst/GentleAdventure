(** printing nat %\ensuremath{\mathbb{N}}% #&#8469;# *)
(** printing -> %\ensuremath{\to}% #&#8594;$ *)

(** * This is a template for Coqdoc Coq files *)



(** ** Preliminaries

A Coqdoc file is a regular Coq file with some special comments that
document it and allow the generation of nice looking documentation
files. This file is such an example and it tries to show some of the
markup for coqdoc. For complete documentation go to
https://coq.inria.fr/refman/using/tools/coqdoc.html

To generate html:

<< coqdoc --html -d <output directory> -s --no-index *.v >>

To generate latex: (* these non document comments do not appear in the
                      output *)

<< coqdoc --latex -d <output directory> -s --no-index *.v >>

Note:

  - << -s >> removes the title from the file

  - << --no-index >> prevents the generation of an index files with
  pointers to all the definitions.

---- (* this generates a horizontal rule *)


*)


(** ** Some code *)

(** This is a definition for natural numbers *)

Inductive nat :=
| Z : nat
| S : nat -> nat
.

(** This defines natural numbers ([nat]) in a _boring way_. *)
(* _italics_ is for emphasis, and [...] for quoting Coq code inside of
the documentation comments. *)


(** Notice how the first two lines insert some pretty printing to the
name nat, and the ->. To insert more just use the same command passing
the token to pretty print, the latex pretty printing and the html
pretty printint. *)

(** ** Some markup *)

(** We can do shopping lists by:
- milk
- potatoes
- olive oil
- cannoli #(don't forget the <a href="https://www.youtube.com/watch?v=-8jREM_AZgQ">cannoli</a>)#
*)

(* Note how you can include inline html with #...# and latex inline
with %...%, finally $...$ for latex in math mode *)

(** ** More *)

(* we can use this to hide ugly code *)

(* begin hide *)

Definition one := 1.

(* end hide *)

(** If we want to show something as a detail we can do the following:
*)

(* begin details : Click the arrow if you are really curious. *)

Definition two := one + one.

(** This is useful for more interactive stuff in html *)

(* end details *)
