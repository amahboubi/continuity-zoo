# continuity-zoo

Putting the pdf of the paper in this directory will make the links to the coqdoc html files work.
The html files are pre-build.
To rebuild all Coq files, do

```bash
opam switch create continuity --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
opam repo add coq-released https://coq.inria.fr/opam/released
opam install  coq.8.20.1 coq-mathcomp-ssreflect coq-mathcomp-zify coq-equations 
make
```

To rebuild all html files, do
```bash
make html
```

The main file is theories/continuity_zoo_Prop.v. It contains several different definitions of continuity as well as proofs regarding how they relate with each other.

kawai2018.v contains two definitions of continuity coming from Kawai's *Principles of bar induction and continuity on Baire space*.

Brouwer_ext.v contains two other, quite technical, definitions of continuity, only useful for later proofs but without much mathematical intuition.

The file extra_principles.v contains concepts relevant to Bar Induction, borrrowed from Étienne Miquey's formalization of Brede-Herbelin's LICS 21 paper *On the logical structure of choice and bar induction principles*. 

File BI.v uses these concepts to relate variants of Bar Induction to the equivalence between continuity definitions.

Finally, the **Old** folder contains an old version of continuity_zoo.v, where existentials live in Type rather than in Prop. The **Brede-Herbelin** folder contains an attempt at formalizing parts of Brede-Herbelin's LICS 21 paper, which led to the discovery of a mistake in the paper.
