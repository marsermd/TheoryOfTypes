ocamlc -g -I ../hw1/ ../hw1/Lambda.ml ../hw1/hw1.ml hw1_reduction.mli hw1_reduction.ml -o out.out
chmod +x out.out
OCAMLRUNPARAM=b ./out.out
