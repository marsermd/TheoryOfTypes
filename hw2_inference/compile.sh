ocamlc -g -I ../hw1/ ../hw1/Lambda.ml ../hw1/hw1.ml \
	-I ../hw1_reduction/ ../hw1_reduction/hw1_reduction.ml \
	-I ../hw2_unify/ ../hw2_unify/hw2_unify.ml \
	 hw2_inference.mli hw2_inference.ml \
	-o out.out
chmod +x out.out
OCAMLRUNPARAM=b ./out.out
