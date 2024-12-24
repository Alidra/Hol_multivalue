Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import option_INDUCT_term_abbrevs.
Require Import thm1069367_spec.
Require Import thm1069368_spec.
Require Import thm1069415_spec.
Require Import thm1069419_spec.
Require Import thm1069766_spec.
Require Import thm1070118_spec.
Lemma lem1070119 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term1 A NONE' SOME' option' P.
Proof. exact (@lem1069368 A option' NONE' SOME' h1 (term2 A option' P)). Qed.
Lemma lem1070120 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) (option' : type1338 A) (P : type1160 A) : (term1 A NONE' SOME' option' P) = (term3 A NONE' SOME' option' P).
Proof. exact (eq_refl (term1 A NONE' SOME' option' P)). Qed.
Lemma lem1070121 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term3 A NONE' SOME' option' P.
Proof. exact (EQ_MP (@lem1070120 A NONE' SOME' option' P) (@lem1070119 A P option' NONE' SOME' h1)). Qed.
Lemma lem1070122 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term4 A option' SOME'.
Proof. exact (proj2 (@lem1069367 A option' NONE' SOME' h1)). Qed.
Lemma lem1070126 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) : (term5 A option' P NONE') = (term6 A option' P NONE').
Proof. exact (eq_refl (term5 A option' P NONE')). Qed.
Lemma lem1070128 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : option' NONE'.
Proof. exact (proj1 (@lem1069367 A option' NONE' SOME' h1)). Qed.
Lemma lem1070130 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term7 A)) : (@_mk_option A NONE') = (@None A).
Proof. exact (SYM (@lem1069766 A NONE' h1)). Qed.
Lemma lem1070131 {A : Type'} (P : type1160 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1070132 {A : Type'} (P : type1160 A) (NONE' : recspace A) (h1 : NONE' = (term7 A)) : (term8 A P NONE') = (P (@None A)).
Proof. exact (MK_COMB (@lem1070131 A P) (@lem1070130 A NONE' h1)). Qed.
Lemma lem1070133 {A : Type'} (option' : type1338 A) (NONE' : recspace A) : (term9 A option' NONE') = (term9 A option' NONE').
Proof. exact (eq_refl (term9 A option' NONE')). Qed.
Lemma lem1070134 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) (h1 : NONE' = (term7 A)) : (term6 A option' P NONE') = (term10 A option' NONE' P).
Proof. exact (MK_COMB (@lem1070133 A option' NONE') (@lem1070132 A P NONE' h1)). Qed.
Lemma lem1070135 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) : (term11 A option' P NONE') = (term11 A option' P NONE').
Proof. exact (eq_refl (term11 A option' P NONE')). Qed.
Lemma lem1070136 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) (h1 : NONE' = (term7 A)) : ((term5 A option' P NONE') = (term6 A option' P NONE')) = ((term5 A option' P NONE') = (term10 A option' NONE' P)).
Proof. exact (MK_COMB (@lem1070135 A option' P NONE') (@lem1070134 A option' P NONE' h1)). Qed.
Lemma lem1070137 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) (h1 : NONE' = (term7 A)) : (term5 A option' P NONE') = (term10 A option' NONE' P).
Proof. exact (EQ_MP (@lem1070136 A option' P NONE' h1) (@lem1070126 A option' P NONE')). Qed.
Lemma lem1070138 {A : Type'} (P : type1160 A) (h1 : P (@None A)) : P (@None A).
Proof. exact (h1). Qed.
Lemma lem1070139 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : P (@None A)) (h2 : option' = (term0 A NONE' SOME')) : term10 A option' NONE' P.
Proof. exact (conj (@lem1070128 A option' NONE' SOME' h2) (@lem1070138 A P h1)). Qed.
Lemma lem1070140 {A : Type'} (option' : type1338 A) (P : type1160 A) (NONE' : recspace A) (h1 : NONE' = (term7 A)) : (term10 A option' NONE' P) = (term5 A option' P NONE').
Proof. exact (SYM (@lem1070137 A option' P NONE' h1)). Qed.
Lemma lem1070141 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : P (@None A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : term5 A option' P NONE'.
Proof. exact (EQ_MP (@lem1070140 A option' P NONE' h3) (@lem1070139 A P option' NONE' SOME' h1 h2)). Qed.
Lemma lem1070142 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : option' = (term0 A NONE' SOME')) (h2 : NONE' = (term7 A)) : term12 A option' P NONE'.
Proof. exact (fun h0 : P (@None A) => @lem1070141 A P option' SOME' NONE' h0 h1 h2). Qed.
Lemma lem1070143 {A : Type'} (option' : type1338 A) (P : type1160 A) (SOME' : type1432 A) (a : A) : (term13 A option' P SOME' a) = (term14 A option' P SOME' a).
Proof. exact (eq_refl (term13 A option' P SOME' a)). Qed.
Lemma lem1070144 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term15 A option' SOME' a.
Proof. exact (@lem1070122 A option' NONE' SOME' h1 a). Qed.
Lemma lem1070145 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term15 A option' SOME' a) = (term16 A option' SOME' a).
Proof. exact (eq_refl (term15 A option' SOME' a)). Qed.
Lemma lem1070148 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term16 A option' SOME' a.
Proof. exact (EQ_MP (@lem1070145 A option' SOME' a) (@lem1070144 A a option' NONE' SOME' h1)). Qed.
Lemma lem1070149 {A : Type'} (a : A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term16 A option' SOME' a.
Proof. exact (@lem1070148 A a option' NONE' SOME' h1). Qed.
Lemma lem1070151 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term18 A SOME' a) = (@Some A a).
Proof. exact (SYM (@lem1070118 A a SOME' h1)). Qed.
Lemma lem1070152 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term18 A SOME' a) = (@Some A a).
Proof. exact (@lem1070151 A a SOME' h1). Qed.
Lemma lem1070153 {A : Type'} (P : type1160 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1070154 {A : Type'} (P : type1160 A) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term19 A P SOME' a) = (term20 A P a).
Proof. exact (MK_COMB (@lem1070153 A P) (@lem1070152 A a SOME' h1)). Qed.
Lemma lem1070155 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (a : A) : (term21 A option' SOME' a) = (term21 A option' SOME' a).
Proof. exact (eq_refl (term21 A option' SOME' a)). Qed.
Lemma lem1070156 {A : Type'} (option' : type1338 A) (P : type1160 A) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term14 A option' P SOME' a) = (term22 A option' SOME' P a).
Proof. exact (MK_COMB (@lem1070155 A option' SOME' a) (@lem1070154 A P a SOME' h1)). Qed.
Lemma lem1070157 {A : Type'} (option' : type1338 A) (P : type1160 A) (SOME' : type1432 A) (a : A) : (term23 A option' P SOME' a) = (term23 A option' P SOME' a).
Proof. exact (eq_refl (term23 A option' P SOME' a)). Qed.
Lemma lem1070158 {A : Type'} (option' : type1338 A) (P : type1160 A) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : ((term13 A option' P SOME' a) = (term14 A option' P SOME' a)) = ((term13 A option' P SOME' a) = (term22 A option' SOME' P a)).
Proof. exact (MK_COMB (@lem1070157 A option' P SOME' a) (@lem1070156 A option' P a SOME' h1)). Qed.
Lemma lem1070159 {A : Type'} (option' : type1338 A) (P : type1160 A) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term13 A option' P SOME' a) = (term22 A option' SOME' P a).
Proof. exact (EQ_MP (@lem1070158 A option' P a SOME' h1) (@lem1070143 A option' P SOME' a)). Qed.
Lemma lem1070160 {A : Type'} (P : type1160 A) (h1 : term24 A P) : term24 A P.
Proof. exact (h1). Qed.
Lemma lem1070161 {A : Type'} (a : A) (P : type1160 A) (h1 : term24 A P) : term25 A P a.
Proof. exact (@lem1070160 A P h1 a). Qed.
Lemma lem1070162 {A : Type'} (P : type1160 A) (a : A) : (term25 A P a) = (term20 A P a).
Proof. exact (eq_refl (term25 A P a)). Qed.
Lemma lem1070163 {A : Type'} (a : A) (P : type1160 A) (h1 : term24 A P) : term20 A P a.
Proof. exact (EQ_MP (@lem1070162 A P a) (@lem1070161 A a P h1)). Qed.
Lemma lem1070164 {A : Type'} (a : A) (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term24 A P) (h2 : option' = (term0 A NONE' SOME')) : term22 A option' SOME' P a.
Proof. exact (conj (@lem1070149 A a option' NONE' SOME' h2) (@lem1070163 A a P h1)). Qed.
Lemma lem1070165 {A : Type'} (option' : type1338 A) (P : type1160 A) (a : A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : (term22 A option' SOME' P a) = (term13 A option' P SOME' a).
Proof. exact (SYM (@lem1070159 A option' P a SOME' h1)). Qed.
Lemma lem1070166 {A : Type'} (a : A) (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term24 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) : term13 A option' P SOME' a.
Proof. exact (EQ_MP (@lem1070165 A option' P a SOME' h2) (@lem1070164 A a P option' NONE' SOME' h1 h3)). Qed.
Lemma lem1070167 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term24 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) : term26 A option' P SOME'.
Proof. exact (fun a : A => @lem1070166 A a P option' NONE' SOME' h1 h2 h3). Qed.
Lemma lem1070168 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) : term27 A option' P SOME'.
Proof. exact (fun h0 : term24 A P => @lem1070167 A P option' NONE' SOME' h0 h1 h2). Qed.
Lemma lem1070169 {A : Type'} (P : type1160 A) (h1 : term28 A P) : term28 A P.
Proof. exact (h1). Qed.
Lemma lem1070170 {A : Type'} (P : type1160 A) (h1 : term28 A P) : term24 A P.
Proof. exact (proj2 (@lem1070169 A P h1)). Qed.
Lemma lem1070171 {A : Type'} (P : type1160 A) (h1 : term28 A P) : P (@None A).
Proof. exact (proj1 (@lem1070169 A P h1)). Qed.
Lemma lem1070172 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : term5 A option' P NONE'.
Proof. exact (@lem1070142 A P option' SOME' NONE' h2 h3 (@lem1070171 A P h1)). Qed.
Lemma lem1070173 {A : Type'} (P : type1160 A) (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) : term26 A option' P SOME'.
Proof. exact (@lem1070168 A P option' NONE' SOME' h2 h3 (@lem1070170 A P h1)). Qed.
Lemma lem1070174 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term29 A NONE' option' P SOME'.
Proof. exact (conj (@lem1070172 A P option' SOME' NONE' h1 h3 h4) (@lem1070173 A P option' NONE' SOME' h1 h2 h3)). Qed.
Lemma lem1070175 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term30 A option' P.
Proof. exact (@lem1070121 A P option' NONE' SOME' h3 (@lem1070174 A P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070176 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term31 A option' P x.
Proof. exact (@lem1070175 A P option' SOME' NONE' h1 h2 h3 h4 (@_dest_option A x)). Qed.
Lemma lem1070177 {A : Type'} (option' : type1338 A) (P : type1160 A) (x : option A) : (term31 A option' P x) = (term32 A option' P x).
Proof. exact (eq_refl (term31 A option' P x)). Qed.
Lemma lem1070178 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term32 A option' P x.
Proof. exact (EQ_MP (@lem1070177 A option' P x) (@lem1070176 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070180 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : (option' r) = ((term33 A r) = r).
Proof. exact (TRANS (@lem1069419 A r option' SOME' NONE' h1 h2 h3) (@lem1069415 A r)). Qed.
Lemma lem1070181 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : (option' r) = ((term33 A r) = r).
Proof. exact (@lem1070180 A r option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070182 {A : Type'} (x : option A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : (term34 A option' x) = ((term35 A x) = (@_dest_option A x)).
Proof. exact (@lem1070181 A (@_dest_option A x) option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070184 {A : Type'} (x : option A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : (term36 A option' x) = (term37 A x).
Proof. exact (MK_COMB (@lem1070183) (@lem1070182 A x option' SOME' NONE' h1 h2 h3)). Qed.
Lemma lem1070185 {A : Type'} (option' : type1338 A) (P : type1160 A) (x : option A) : (term38 A option' P x) = (term38 A option' P x).
Proof. exact (eq_refl (term38 A option' P x)). Qed.
Lemma lem1070186 {A : Type'} (P : type1160 A) (x : option A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : (term32 A option' P x) = (term39 A option' P x).
Proof. exact (MK_COMB (@lem1070184 A x option' SOME' NONE' h1 h2 h3) (@lem1070185 A option' P x)). Qed.
Lemma lem1070187 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term39 A option' P x.
Proof. exact (EQ_MP (@lem1070186 A P x option' SOME' NONE' h2 h3 h4) (@lem1070178 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070189 {A : Type'} (a : option A) : (term40 A a) = a.
Proof. exact (@axiom_13 A a). Qed.
Lemma lem1070190 {A : Type'} (a : option A) : (term40 A a) = a.
Proof. exact (@lem1070189 A a). Qed.
Lemma lem1070191 {A : Type'} (x : option A) : (term40 A x) = x.
Proof. exact (@lem1070190 A x). Qed.
Lemma lem1070192 {A : Type'} : (@_dest_option A) = (@_dest_option A).
Proof. exact (eq_refl (@_dest_option A)). Qed.
Lemma lem1070193 {A : Type'} (x : option A) : (term35 A x) = (@_dest_option A x).
Proof. exact (MK_COMB (@lem1070192 A) (@lem1070191 A x)). Qed.
Lemma lem1070194 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1070195 {A : Type'} (x : option A) : (term41 A x) = (term42 A x).
Proof. exact (MK_COMB (@lem1070194 A) (@lem1070193 A x)). Qed.
Lemma lem1070196 {A : Type'} (x : option A) : (@_dest_option A x) = (@_dest_option A x).
Proof. exact (eq_refl (@_dest_option A x)). Qed.
Lemma lem1070197 {A : Type'} (x : option A) : ((term35 A x) = (@_dest_option A x)) = ((@_dest_option A x) = (@_dest_option A x)).
Proof. exact (MK_COMB (@lem1070195 A x) (@lem1070196 A x)). Qed.
Lemma lem1070198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1070199 {A : Type'} (x : option A) : (term37 A x) = (term43 A x).
Proof. exact (MK_COMB (@lem1070198) (@lem1070197 A x)). Qed.
Lemma lem1070200 {A : Type'} (option' : type1338 A) (P : type1160 A) (x : option A) : (term38 A option' P x) = (term38 A option' P x).
Proof. exact (eq_refl (term38 A option' P x)). Qed.
Lemma lem1070201 {A : Type'} (option' : type1338 A) (P : type1160 A) (x : option A) : (term39 A option' P x) = (term44 A option' P x).
Proof. exact (MK_COMB (@lem1070199 A x) (@lem1070200 A option' P x)). Qed.
Lemma lem1070202 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term44 A option' P x.
Proof. exact (EQ_MP (@lem1070201 A option' P x) (@lem1070187 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070203 {A : Type'} (x : option A) : (@_dest_option A x) = (@_dest_option A x).
Proof. exact (eq_refl (@_dest_option A x)). Qed.
Lemma lem1070204 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term38 A option' P x.
Proof. exact (@lem1070202 A x P option' SOME' NONE' h1 h2 h3 h4 (@lem1070203 A x)). Qed.
Lemma lem1070205 {A : Type'} (option' : type1338 A) (P : type1160 A) (x : option A) : (term38 A option' P x) = (term45 A option' P x).
Proof. exact (eq_refl (term38 A option' P x)). Qed.
Lemma lem1070206 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term45 A option' P x.
Proof. exact (EQ_MP (@lem1070205 A option' P x) (@lem1070204 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070207 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term46 A P x.
Proof. exact (proj2 (@lem1070206 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070209 {A : Type'} (a : option A) : (term40 A a) = a.
Proof. exact (@axiom_13 A a). Qed.
Lemma lem1070210 {A : Type'} (a : option A) : (term40 A a) = a.
Proof. exact (@lem1070209 A a). Qed.
Lemma lem1070211 {A : Type'} (x : option A) : (term40 A x) = x.
Proof. exact (@lem1070210 A x). Qed.
Lemma lem1070212 {A : Type'} (P : type1160 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1070213 {A : Type'} (P : type1160 A) (x : option A) : (term46 A P x) = (P x).
Proof. exact (MK_COMB (@lem1070212 A P) (@lem1070211 A x)). Qed.
Lemma lem1070214 {A : Type'} (x : option A) (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : P x.
Proof. exact (EQ_MP (@lem1070213 A P x) (@lem1070207 A x P option' SOME' NONE' h1 h2 h3 h4)). Qed.
Lemma lem1070215 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : term28 A P) (h2 : SOME' = (term17 A)) (h3 : option' = (term0 A NONE' SOME')) (h4 : NONE' = (term7 A)) : term47 A P.
Proof. exact (fun x : option A => @lem1070214 A x P option' SOME' NONE' h1 h2 h3 h4). Qed.
Lemma lem1070216 {A : Type'} (P : type1160 A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : term48 A P.
Proof. exact (fun h0 : term28 A P => @lem1070215 A P option' SOME' NONE' h0 h1 h2 h3). Qed.
Lemma lem1070217 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term7 A)) : term49 A.
Proof. exact (fun P : type1160 A => @lem1070216 A P option' SOME' NONE' h1 h2 h3). Qed.
Lemma lem1070218 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term17 A)) (h2 : NONE' = (term7 A)) : term50 A option' NONE' SOME'.
Proof. exact (fun h0 : option' = (term0 A NONE' SOME') => @lem1070217 A option' SOME' NONE' h1 h0 h2). Qed.
Lemma lem1070219 {A : Type'} : (term7 A) = (term7 A).
Proof. exact (eq_refl (term7 A)). Qed.
Lemma lem1070220 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : term51 A option' NONE' SOME'.
Proof. exact (fun h0 : NONE' = (term7 A) => @lem1070218 A option' SOME' NONE' h1 h0). Qed.
Lemma lem1070221 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : term52 A option' SOME'.
Proof. exact (@lem1070220 A option' (term7 A) SOME' h1). Qed.
Lemma lem1070222 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : SOME' = (term17 A)) : term53 A option' SOME'.
Proof. exact (@lem1070221 A option' SOME' h1 (@lem1070219 A)). Qed.
Lemma lem1070223 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (eq_refl (term17 A)). Qed.
Lemma lem1070224 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) : term54 A option' SOME'.
Proof. exact (fun h0 : SOME' = (term17 A) => @lem1070222 A option' SOME' h0). Qed.
Lemma lem1070225 {A : Type'} (option' : type1338 A) : term55 A option'.
Proof. exact (@lem1070224 A option' (term17 A)). Qed.
Lemma lem1070226 {A : Type'} (option' : type1338 A) : term56 A option'.
Proof. exact (@lem1070225 A option' (@lem1070223 A)). Qed.
Lemma lem1070227 {A : Type'} (option' : type1338 A) (h1 : option' = (term57 A)) : option' = (term57 A).
Proof. exact (h1). Qed.
Lemma lem1070228 {A : Type'} (option' : type1338 A) (h1 : option' = (term57 A)) : term49 A.
Proof. exact (@lem1070226 A option' (@lem1070227 A option' h1)). Qed.
Lemma lem1070229 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (eq_refl (term57 A)). Qed.
Lemma lem1070230 {A : Type'} (option' : type1338 A) : term56 A option'.
Proof. exact (fun h0 : option' = (term57 A) => @lem1070228 A option' h0). Qed.
Lemma lem1070231 {A : Type'} : term58 A.
Proof. exact (@lem1070230 A (term57 A)). Qed.
Lemma lem1070232 {A : Type'} : term49 A.
Proof. exact (@lem1070231 A (@lem1070229 A)). Qed.
