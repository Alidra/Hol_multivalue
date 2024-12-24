Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261376_term_abbrevs.
Require Import IN_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7260963_spec.
Require Import thm7260972_spec.
Lemma lem7261112 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7261113 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7261114 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7261113 m) (@lem7261112 m)). Qed.
Lemma lem7261115 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7261114 m n). Qed.
Lemma lem7261116 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7261117 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7261116 m n) (@lem7261115 m n)). Qed.
Lemma lem7261118 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7261117 m n p). Qed.
Lemma lem7261119 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7261159 (i : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term8 a b f g i.
Proof. exact (@lem7260963 a b f g h1 i). Qed.
Lemma lem7261160 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term8 a b f g i) = (term9 a b f g i).
Proof. exact (eq_refl (term8 a b f g i)). Qed.
Lemma lem7261161 (i : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term9 a b f g i.
Proof. exact (EQ_MP (@lem7261160 a b f g i) (@lem7261159 i a b f g h1)). Qed.
Lemma lem7261162 (a : nat) (i : nat) (b : nat) (h1 : term6 a i b) : term6 a i b.
Proof. exact (h1). Qed.
Lemma lem7261163 (f : nat -> real) (g : nat -> real) (a : nat) (i : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a i b) : (f i) = (g i).
Proof. exact (@lem7261161 i a b f g h1 (@lem7261162 a i b h2)). Qed.
Lemma lem7261176 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term10 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7261177 (p : Prop) (q : Prop) (p' : Prop) : term11 p q p'.
Proof. exact (fun q' : Prop => @lem7261176 p q p' q'). Qed.
Lemma lem7261178 (p : Prop) (q : Prop) : term12 p q.
Proof. exact (fun p' : Prop => @lem7261177 p q p'). Qed.
Lemma lem7261179 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) : term13 a b f g x.
Proof. exact (@lem7261178 (term5 x a b) ((term14 f x) = (g x))). Qed.
Lemma lem7261180 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : term15 a b f g x p'.
Proof. exact (@lem7261179 a b f g x p'). Qed.
Lemma lem7261181 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : (term15 a b f g x p') = (term16 a b f g x p').
Proof. exact (eq_refl (term15 a b f g x p')). Qed.
Lemma lem7261182 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : term16 a b f g x p'.
Proof. exact (EQ_MP (@lem7261181 a b f g x p') (@lem7261180 a b f g x p')). Qed.
Lemma lem7261183 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term17 a b f g x p' q'.
Proof. exact (@lem7261182 a b f g x p' q'). Qed.
Lemma lem7261184 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : (term17 a b f g x p' q') = (term18 a b f g x p' q').
Proof. exact (eq_refl (term17 a b f g x p' q')). Qed.
Lemma lem7261185 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term18 a b f g x p' q'.
Proof. exact (EQ_MP (@lem7261184 a b f g x p' q') (@lem7261183 a b f g x p' q')). Qed.
Lemma lem7261187 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7261119 m p n) (@lem7261118 m n p)). Qed.
Lemma lem7261188 (a : nat) (x : nat) (b : nat) : (term5 x a b) = (term6 a x b).
Proof. exact (@lem7261187 a x b). Qed.
Lemma lem7261191 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (q' : Prop) : term19 f g a x b q'.
Proof. exact (@lem7261185 a b f g x (term6 a x b) q'). Qed.
Lemma lem7261192 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (q' : Prop) : term20 f g a x b q'.
Proof. exact (@lem7261191 f g a x b q' (@lem7261188 a x b)). Qed.
Lemma lem7261193 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : term6 a x b.
Proof. exact (h1). Qed.
Lemma lem7261194 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : Peano.le x b.
Proof. exact (proj2 (@lem7261193 a x b h1)). Qed.
Lemma lem7261195 (x : nat) (b : nat) : (Peano.le x b) = ((Peano.le x b) = True).
Proof. exact (@lem7 (Peano.le x b)). Qed.
Lemma lem7261197 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : Peano.le a x.
Proof. exact (proj1 (@lem7261193 a x b h1)). Qed.
Lemma lem7261198 (a : nat) (x : nat) : (Peano.le a x) = ((Peano.le a x) = True).
Proof. exact (@lem7 (Peano.le a x)). Qed.
Lemma lem7261203 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7261204 (f : nat -> real) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem7261203 nat real f y). Qed.
Lemma lem7261205 (f : nat -> real) (x : nat) : (term14 f x) = (f x).
Proof. exact (@lem7261204 f x). Qed.
Lemma lem7261207 (i : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term9 a b f g i.
Proof. exact (fun h0 : term6 a i b => @lem7261163 f g a i b h1 h0). Qed.
Lemma lem7261208 (x : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term9 a b f g x.
Proof. exact (@lem7261207 x a b f g h1). Qed.
Lemma lem7261212 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : (Peano.le a x) = True.
Proof. exact (EQ_MP (@lem7261198 a x) (@lem7261197 a x b h1)). Qed.
Lemma lem7261213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7261214 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : (term22 a x) = (and True).
Proof. exact (MK_COMB (@lem7261213) (@lem7261212 a x b h1)). Qed.
Lemma lem7261216 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : (Peano.le x b) = True.
Proof. exact (EQ_MP (@lem7261195 x b) (@lem7261194 a x b h1)). Qed.
Lemma lem7261217 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : (term6 a x b) = (True /\ True).
Proof. exact (MK_COMB (@lem7261214 a x b h1) (@lem7261216 a x b h1)). Qed.
Lemma lem7261219 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7261220 : (True /\ True) = True.
Proof. exact (@lem7261219 True). Qed.
Lemma lem7261221 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : (term6 a x b) = True.
Proof. exact (TRANS (@lem7261217 a x b h1) (@lem7261220)). Qed.
Lemma lem7261222 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : True = (term6 a x b).
Proof. exact (SYM (@lem7261221 a x b h1)). Qed.
Lemma lem7261223 (a : nat) (x : nat) (b : nat) (h1 : term6 a x b) : term6 a x b.
Proof. exact (EQ_MP (@lem7261222 a x b h1) (@lem0)). Qed.
Lemma lem7261224 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a x b) : (f x) = (g x).
Proof. exact (@lem7261208 x a b f g h1 (@lem7261223 a x b h2)). Qed.
Lemma lem7261225 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a x b) : (term14 f x) = (g x).
Proof. exact (TRANS (@lem7261205 f x) (@lem7261224 f g a x b h1 h2)). Qed.
Lemma lem7261226 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7261227 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a x b) : (term23 f x) = (term24 g x).
Proof. exact (MK_COMB (@lem7261226) (@lem7261225 f g a x b h1 h2)). Qed.
Lemma lem7261228 (g : nat -> real) (x : nat) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem7261229 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a x b) : ((term14 f x) = (g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem7261227 f g a x b h1 h2) (@lem7261228 g x)). Qed.
Lemma lem7261231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7261232 (x : real) : (x = x) = True.
Proof. exact (@lem7261231 real x). Qed.
Lemma lem7261233 (g : nat -> real) (x : nat) : ((g x) = (g x)) = True.
Proof. exact (@lem7261232 (g x)). Qed.
Lemma lem7261234 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) (h1 : term7 a b f g) (h2 : term6 a x b) : ((term14 f x) = (g x)) = True.
Proof. exact (TRANS (@lem7261229 f g a x b h1 h2) (@lem7261233 g x)). Qed.
Lemma lem7261235 (x : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term25 a b f g x.
Proof. exact (fun h0 : term6 a x b => @lem7261234 f g a x b h1 h0). Qed.
Lemma lem7261236 (f : nat -> real) (g : nat -> real) (a : nat) (x : nat) (b : nat) : term26 f g a x b.
Proof. exact (@lem7261192 f g a x b True). Qed.
Lemma lem7261237 (x : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term27 a b f g x) = (term28 a x b).
Proof. exact (@lem7261236 f g a x b (@lem7261235 x a b f g h1)). Qed.
Lemma lem7261239 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7261240 (a : nat) (x : nat) (b : nat) : (term28 a x b) = True.
Proof. exact (@lem7261239 (term6 a x b)). Qed.
Lemma lem7261241 (x : nat) (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term27 a b f g x) = True.
Proof. exact (TRANS (@lem7261237 x a b f g h1) (@lem7261240 a x b)). Qed.
Lemma lem7261242 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term29 a b f g) = term30.
Proof. exact (fun_ext (fun x : nat => @lem7261241 x a b f g h1)). Qed.
Lemma lem7261243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7261244 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term31 a b f g) = term32.
Proof. exact (MK_COMB (@lem7261243) (@lem7261242 a b f g h1)). Qed.
Lemma lem7261246 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7261247 (t : Prop) : (term34 t) = t.
Proof. exact (@lem7261246 nat t). Qed.
Lemma lem7261248 : term32 = True.
Proof. exact (@lem7261247 True). Qed.
Lemma lem7261249 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term31 a b f g) = True.
Proof. exact (TRANS (@lem7261244 a b f g h1) (@lem7261248)). Qed.
Lemma lem7261250 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : True = (term31 a b f g).
Proof. exact (SYM (@lem7261249 a b f g h1)). Qed.
Lemma lem7261251 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : term31 a b f g.
Proof. exact (EQ_MP (@lem7261250 a b f g h1) (@lem0)). Qed.
Lemma lem7261376 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term7 a b f g) : (term35 a b f) = (term36 a b g).
Proof. exact (@lem7260972 f a b g (@lem7261251 a b f g h1)). Qed.
