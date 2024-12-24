Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_PCROSS_term_abbrevs.
Require Import BIJECTIONS_HAS_SIZE_EQ_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FSTCART_PASTECART_spec.
Require Import HAS_SIZE_PRODUCT_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import PASTECART_FST_SND_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm1157_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm8003920_spec.
Lemma lem8026124 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7648197 A M N x). Qed.
Lemma lem8026125 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8026126 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8026125 A M N x) (@lem8026124 A M N x)). Qed.
Lemma lem8026127 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8026126 A M N x y). Qed.
Lemma lem8026128 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = ((term3 A M N x y) = y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8026130 {A M N : Type'} (x : cart A M) : term4 A M N x.
Proof. exact (@lem7643282 A M N x). Qed.
Lemma lem8026131 {A M N : Type'} (x : cart A M) : (term4 A M N x) = (term5 A M N x).
Proof. exact (eq_refl (term4 A M N x)). Qed.
Lemma lem8026132 {A M N : Type'} (x : cart A M) : term5 A M N x.
Proof. exact (EQ_MP (@lem8026131 A M N x) (@lem8026130 A M N x)). Qed.
Lemma lem8026133 {A M N : Type'} (x : cart A M) (y : cart A N) : term6 A M N x y.
Proof. exact (@lem8026132 A M N x y). Qed.
Lemma lem8026134 {A M N : Type'} (y : cart A N) (x : cart A M) : (term6 A M N x y) = ((term7 A M N x y) = x).
Proof. exact (eq_refl (term6 A M N x y)). Qed.
Lemma lem8026136 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : term8 _140390 _140392 _140395 z.
Proof. exact (@lem7659572 _140390 _140392 _140395 z). Qed.
Lemma lem8026137 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term8 _140390 _140392 _140395 z) = ((term9 _140390 _140392 _140395 z) = z).
Proof. exact (eq_refl (term8 _140390 _140392 _140395 z)). Qed.
Lemma lem8026139 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term10 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem8026140 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term10 _88435 _88436 P) = (term11 _88435 _88436 P).
Proof. exact (eq_refl (term10 _88435 _88436 P)). Qed.
Lemma lem8026141 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term11 _88435 _88436 P.
Proof. exact (EQ_MP (@lem8026140 _88435 _88436 P) (@lem8026139 _88435 _88436 P)). Qed.
Lemma lem8026142 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term12 _88435 _88436 P a.
Proof. exact (@lem8026141 _88435 _88436 P a). Qed.
Lemma lem8026143 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term12 _88435 _88436 P a) = (term13 _88435 _88436 P a).
Proof. exact (eq_refl (term12 _88435 _88436 P a)). Qed.
Lemma lem8026144 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term13 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem8026143 _88435 _88436 P a) (@lem8026142 _88435 _88436 P a)). Qed.
Lemma lem8026145 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term14 _88435 _88436 P a b.
Proof. exact (@lem8026144 _88435 _88436 P a b). Qed.
Lemma lem8026146 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term14 _88435 _88436 P a b) = ((term15 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term14 _88435 _88436 P a b)). Qed.
Lemma lem8026148 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term16 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8026149 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term16 _141927 _141928 _141929 s) = (term17 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term16 _141927 _141928 _141929 s)). Qed.
Lemma lem8026150 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term17 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8026149 _141927 _141928 _141929 s) (@lem8026148 _141927 _141928 _141929 s)). Qed.
Lemma lem8026151 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term18 _141927 _141928 _141929 s t.
Proof. exact (@lem8026150 _141927 _141928 _141929 s t). Qed.
Lemma lem8026152 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term18 _141927 _141928 _141929 s t) = (term19 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term18 _141927 _141928 _141929 s t)). Qed.
Lemma lem8026153 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term19 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8026152 _141927 _141928 _141929 s t) (@lem8026151 _141927 _141928 _141929 s t)). Qed.
Lemma lem8026154 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term20 _141927 _141928 _141929 s t x.
Proof. exact (@lem8026153 _141927 _141928 _141929 s t x). Qed.
Lemma lem8026155 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term20 _141927 _141928 _141929 s t x) = (term21 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term20 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8026156 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term21 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8026155 _141927 _141928 _141929 x s t) (@lem8026154 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8026157 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term22 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8026156 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8026158 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term22 _141927 _141928 _141929 x s t y) = ((term23 _141927 _141928 _141929 x y s t) = (term24 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term22 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8026160 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term25 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem8026176 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term26 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem8026160 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem8026177 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term27 _88961 _88962 _89106 Q P.
Proof. exact (@lem8026176 _88961 _88962 _89106 Q P). Qed.
Lemma lem8026178 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term27 _88961 _88962 _89106 Q P) = (term28 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term27 _88961 _88962 _89106 Q P)). Qed.
Lemma lem8026179 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term28 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem8026178 _88961 _88962 _89106 P Q) (@lem8026177 _88961 _88962 _89106 Q P)). Qed.
Lemma lem8026180 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term29 _88961 _88962 _89106 P Q f.
Proof. exact (@lem8026179 _88961 _88962 _89106 P Q f). Qed.
Lemma lem8026181 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term29 _88961 _88962 _89106 P Q f) = ((term30 _88961 _88962 _89106 P f Q) = (term31 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term29 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem8026190 {A B : Type'} (h1 : term32 A B) : term32 A B.
Proof. exact (h1). Qed.
Lemma lem8026191 {A B : Type'} (s : A -> Prop) (h1 : term32 A B) : term33 A B s.
Proof. exact (@lem8026190 A B h1 s). Qed.
Lemma lem8026192 {A B : Type'} (s : A -> Prop) : (term33 A B s) = (term34 A B s).
Proof. exact (eq_refl (term33 A B s)). Qed.
Lemma lem8026193 {A B : Type'} (s : A -> Prop) (h1 : term32 A B) : term34 A B s.
Proof. exact (EQ_MP (@lem8026192 A B s) (@lem8026191 A B s h1)). Qed.
Lemma lem8026194 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term32 A B) : term35 A B s t.
Proof. exact (@lem8026193 A B s h1 t). Qed.
Lemma lem8026195 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term35 A B s t) = (term36 A B s t).
Proof. exact (eq_refl (term35 A B s t)). Qed.
Lemma lem8026196 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term32 A B) : term36 A B s t.
Proof. exact (EQ_MP (@lem8026195 A B s t) (@lem8026194 A B s t h1)). Qed.
Lemma lem8026197 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term32 A B) : term37 A B s t f.
Proof. exact (@lem8026196 A B s t h1 f). Qed.
Lemma lem8026198 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term37 A B s t f) = (term38 A B f s t).
Proof. exact (eq_refl (term37 A B s t f)). Qed.
Lemma lem8026199 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term32 A B) : term38 A B f s t.
Proof. exact (EQ_MP (@lem8026198 A B f s t) (@lem8026197 A B s t f h1)). Qed.
Lemma lem8026200 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (h1 : term32 A B) : term39 A B f s t g.
Proof. exact (@lem8026199 A B f s t h1 g). Qed.
Lemma lem8026201 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : (term39 A B f s t g) = (term40 A B f g s t).
Proof. exact (eq_refl (term39 A B f s t g)). Qed.
Lemma lem8026202 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : term32 A B) : term40 A B f g s t.
Proof. exact (EQ_MP (@lem8026201 A B f g s t) (@lem8026200 A B f s t g h1)). Qed.
Lemma lem8026203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B t s f g) : term41 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem8026204 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term32 A B) (h2 : term41 A B t s f g) : term42 A B s t.
Proof. exact (@lem8026202 A B f g s t h1 (@lem8026203 A B t s f g h2)). Qed.
Lemma lem8026205 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B t s f g) : term43 A B s t.
Proof. exact (fun h0 : term32 A B => @lem8026204 A B t s f g h0 h1). Qed.
Lemma lem8026206 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term44 A B t s f) : term44 A B t s f.
Proof. exact (h1). Qed.
Lemma lem8026207 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term44 A B t s f) : term43 A B s t.
Proof. exact (ex_elim (@lem8026206 A B t s f h1) (fun g : B -> A => fun h0 : term45 A B t s f g => @lem8026205 A B t s f g h0)). Qed.
Lemma lem8026208 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term46 A B t s) : term46 A B t s.
Proof. exact (h1). Qed.
Lemma lem8026209 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term46 A B t s) : term43 A B s t.
Proof. exact (ex_elim (@lem8026208 A B t s h1) (fun f : A -> B => fun h0 : term47 A B t s f => @lem8026207 A B t s f h0)). Qed.
Lemma lem8026210 {A B : Type'} (h1 : term32 A B) : term32 A B.
Proof. exact (h1). Qed.
Lemma lem8026211 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term32 A B) (h2 : term46 A B t s) : term42 A B s t.
Proof. exact (@lem8026209 A B t s h2 (@lem8026210 A B h1)). Qed.
Lemma lem8026212 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term32 A B) : term48 A B s t.
Proof. exact (fun h0 : term46 A B t s => @lem8026211 A B t s h1 h0). Qed.
Lemma lem8026213 {A B : Type'} (s : A -> Prop) (h1 : term32 A B) : term49 A B s.
Proof. exact (fun t : B -> Prop => @lem8026212 A B s t h1). Qed.
Lemma lem8026214 {A B : Type'} (h1 : term32 A B) : term50 A B.
Proof. exact (fun s : A -> Prop => @lem8026213 A B s h1). Qed.
Lemma lem8026215 {A B : Type'} : term51 A B.
Proof. exact (fun h0 : term32 A B => @lem8026214 A B h0). Qed.
Lemma lem8026216 {A B : Type'} : term50 A B.
Proof. exact (@lem8026215 A B (@lem5100070 A B)). Qed.
Lemma lem8026217 {A B : Type'} (s : A -> Prop) : term52 A B s.
Proof. exact (@lem8026216 A B s). Qed.
Lemma lem8026218 {A B : Type'} (s : A -> Prop) : (term52 A B s) = (term49 A B s).
Proof. exact (eq_refl (term52 A B s)). Qed.
Lemma lem8026219 {A B : Type'} (s : A -> Prop) : term49 A B s.
Proof. exact (EQ_MP (@lem8026218 A B s) (@lem8026217 A B s)). Qed.
Lemma lem8026220 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term53 A B s t.
Proof. exact (@lem8026219 A B s t). Qed.
Lemma lem8026221 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term53 A B s t) = (term48 A B s t).
Proof. exact (eq_refl (term53 A B s t)). Qed.
Lemma lem8026223 (a : Prop) (b : Prop) (h1 : term54 a b) : term54 a b.
Proof. exact (h1). Qed.
Lemma lem8026224 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem8026225 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term54 a b) : a -> b.
Proof. exact (@lem8026223 a b h2 (@lem8026224 a b h1)). Qed.
Lemma lem8026226 (a : Prop) (b : Prop) (h1 : a = b) : term55 a b.
Proof. exact (fun h0 : term54 a b => @lem8026225 a b h1 h0). Qed.
Lemma lem8026227 (a : Prop) (b : Prop) (h1 : term54 a b) : term54 a b.
Proof. exact (h1). Qed.
Lemma lem8026228 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term54 a b) : a -> b.
Proof. exact (@lem8026226 a b h1 (@lem8026227 a b h2)). Qed.
Lemma lem8026229 (a : Prop) (b : Prop) (h1 : term54 a b) : term54 a b.
Proof. exact (fun h0 : a = b => @lem8026228 a b h0 h1). Qed.
Lemma lem8026230 (a : Prop) (b : Prop) : term56 a b.
Proof. exact (fun h0 : term54 a b => @lem8026229 a b h0). Qed.
Lemma lem8026232 {A B : Type'} (s : A -> Prop) : term57 A B s.
Proof. exact (@lem4324156 A B s). Qed.
Lemma lem8026233 {A B : Type'} (s : A -> Prop) : (term57 A B s) = (term58 A B s).
Proof. exact (eq_refl (term57 A B s)). Qed.
Lemma lem8026234 {A B : Type'} (s : A -> Prop) : term58 A B s.
Proof. exact (EQ_MP (@lem8026233 A B s) (@lem8026232 A B s)). Qed.
Lemma lem8026235 {A B : Type'} (s : A -> Prop) (m : nat) : term59 A B s m.
Proof. exact (@lem8026234 A B s m). Qed.
Lemma lem8026236 {A B : Type'} (s : A -> Prop) (m : nat) : (term59 A B s m) = (term60 A B s m).
Proof. exact (eq_refl (term59 A B s m)). Qed.
Lemma lem8026237 {A B : Type'} (s : A -> Prop) (m : nat) : term60 A B s m.
Proof. exact (EQ_MP (@lem8026236 A B s m) (@lem8026235 A B s m)). Qed.
Lemma lem8026238 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) : term61 A B s m t.
Proof. exact (@lem8026237 A B s m t). Qed.
Lemma lem8026239 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : (term61 A B s m t) = (term62 A B s t m).
Proof. exact (eq_refl (term61 A B s m t)). Qed.
Lemma lem8026240 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) : term62 A B s t m.
Proof. exact (EQ_MP (@lem8026239 A B s t m) (@lem8026238 A B s m t)). Qed.
Lemma lem8026241 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term63 A B s t m n.
Proof. exact (@lem8026240 A B s t m n). Qed.
Lemma lem8026242 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : (term63 A B s t m n) = (term64 A B s t m n).
Proof. exact (eq_refl (term63 A B s t m n)). Qed.
Lemma lem8026244 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) (h1 : term65 A M N s m t n) : term65 A M N s m t n.
Proof. exact (h1). Qed.
Lemma lem8026246 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (m : nat) (n : nat) : term64 A B s t m n.
Proof. exact (EQ_MP (@lem8026242 A B s t m n) (@lem8026241 A B s t m n)). Qed.
Lemma lem8026247 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : term66 A M N s t m n.
Proof. exact (@lem8026246 (cart A M) (cart A N) s t m n). Qed.
Lemma lem8026248 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) (h1 : term65 A M N s m t n) : term67 A M N s t m n.
Proof. exact (@lem8026247 A M N s t m n (@lem8026244 A M N s m t n h1)). Qed.
Lemma lem8026250 (a : Prop) (b : Prop) : term54 a b.
Proof. exact (@lem8026230 a b (@lem1157 a b)). Qed.
Lemma lem8026251 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : term68 A M N s t m n.
Proof. exact (@lem8026250 (term67 A M N s t m n) (term69 A M N s t m n)). Qed.
Lemma lem8026253 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term48 A B s t.
Proof. exact (EQ_MP (@lem8026221 A B s t) (@lem8026220 A B s t)). Qed.
Lemma lem8026254 {A M N : Type'} (s : type1165 A M N) (t : type16 A M N) : term70 A M N s t.
Proof. exact (@lem8026253 (type1642 A M N) (type2 A M N) s t). Qed.
Lemma lem8026255 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term71 A M N s t.
Proof. exact (@lem8026254 A M N (term72 A M N s t) (@PCROSS A M N s t)). Qed.
Lemma lem8026259 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term30 _88961 _88962 _89106 P f Q) = (term31 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem8026181 _88961 _88962 _89106 P Q f) (@lem8026180 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem8026260 {A M N : Type'} (P : type22 A M N) (Q : type1165 A M N) (f : type21 A M N) : (term73 A M N P f Q) = (term74 A M N P Q f).
Proof. exact (@lem8026259 (cart A N) (cart A M) (type1642 A M N) P Q f). Qed.
Lemma lem8026261 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term75 A M N s t) = (term76 A M N s t).
Proof. exact (@lem8026260 A M N (term77 A M N s t) (term78 A M N s t) (@pair (cart A M) (cart A N))). Qed.
Lemma lem8026262 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term79 A M N s t x) = (term80 A M N x s t).
Proof. exact (eq_refl (term79 A M N s t x)). Qed.
Lemma lem8026263 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026264 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (y : cart A N) : (term81 A M N s t x y) = (term82 A M N x s t y).
Proof. exact (MK_COMB (@lem8026262 A M N x s t) (@lem8026263 A N y)). Qed.
Lemma lem8026265 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term82 A M N x s t y) = (term24 A M N x s y t).
Proof. exact (eq_refl (term82 A M N x s t y)). Qed.
Lemma lem8026266 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term81 A M N s t x y) = (term24 A M N x s y t).
Proof. exact (TRANS (@lem8026264 A M N x s t y) (@lem8026265 A M N x s y t)). Qed.
Lemma lem8026267 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) : (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129) = (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129).
Proof. exact (eq_refl (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129)). Qed.
Lemma lem8026268 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term83 A M N GEN_PVAR_129 s t x y) = (term84 A M N GEN_PVAR_129 x s y t).
Proof. exact (MK_COMB (@lem8026267 A M N GEN_PVAR_129) (@lem8026266 A M N x s y t)). Qed.
Lemma lem8026269 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y).
Proof. exact (eq_refl (@pair (cart A M) (cart A N) x y)). Qed.
Lemma lem8026270 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term85 A M N GEN_PVAR_129 s t x y) = (term86 A M N GEN_PVAR_129 s t x y).
Proof. exact (MK_COMB (@lem8026268 A M N GEN_PVAR_129 x s y t) (@lem8026269 A M N x y)). Qed.
Lemma lem8026271 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) : (term87 A M N GEN_PVAR_129 s t x) = (term88 A M N GEN_PVAR_129 s t x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026270 A M N GEN_PVAR_129 s t x y)). Qed.
Lemma lem8026272 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8026273 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) : (term89 A M N GEN_PVAR_129 s t x) = (term90 A M N GEN_PVAR_129 s t x).
Proof. exact (MK_COMB (@lem8026272 A N) (@lem8026271 A M N GEN_PVAR_129 s t x)). Qed.
Lemma lem8026274 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term91 A M N GEN_PVAR_129 s t) = (term92 A M N GEN_PVAR_129 s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8026273 A M N GEN_PVAR_129 s t x)). Qed.
Lemma lem8026275 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8026276 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term93 A M N GEN_PVAR_129 s t) = (term94 A M N GEN_PVAR_129 s t).
Proof. exact (MK_COMB (@lem8026275 A M) (@lem8026274 A M N GEN_PVAR_129 s t)). Qed.
Lemma lem8026277 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term95 A M N s t) = (term96 A M N s t).
Proof. exact (fun_ext (fun GEN_PVAR_129 : type1642 A M N => @lem8026276 A M N GEN_PVAR_129 s t)). Qed.
Lemma lem8026278 {A M N : Type'} : (@GSPEC (prod (cart A M) (cart A N))) = (@GSPEC (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@GSPEC (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026279 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term97 A M N s t) = (term72 A M N s t).
Proof. exact (MK_COMB (@lem8026278 A M N) (@lem8026277 A M N s t)). Qed.
Lemma lem8026280 {A M N : Type'} (x : type1642 A M N) : (@IN (prod (cart A M) (cart A N)) x) = (@IN (prod (cart A M) (cart A N)) x).
Proof. exact (eq_refl (@IN (prod (cart A M) (cart A N)) x)). Qed.
Lemma lem8026281 {A M N : Type'} (x : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term98 A M N x s t) = (term99 A M N x s t).
Proof. exact (MK_COMB (@lem8026280 A M N x) (@lem8026279 A M N s t)). Qed.
Lemma lem8026282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8026283 {A M N : Type'} (x : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term100 A M N x s t) = (term101 A M N x s t).
Proof. exact (MK_COMB (@lem8026282) (@lem8026281 A M N x s t)). Qed.
Lemma lem8026284 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : type1642 A M N) : (term102 A M N s t x) = (term103 A M N s t x).
Proof. exact (eq_refl (term102 A M N s t x)). Qed.
Lemma lem8026285 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : type1642 A M N) : (term104 A M N s t x) = (term105 A M N s t x).
Proof. exact (MK_COMB (@lem8026283 A M N x s t) (@lem8026284 A M N s t x)). Qed.
Lemma lem8026286 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term106 A M N s t) = (term107 A M N s t).
Proof. exact (fun_ext (fun x : type1642 A M N => @lem8026285 A M N s t x)). Qed.
Lemma lem8026287 {A M N : Type'} : (@all (prod (cart A M) (cart A N))) = (@all (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@all (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026288 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term75 A M N s t) = (term108 A M N s t).
Proof. exact (MK_COMB (@lem8026287 A M N) (@lem8026286 A M N s t)). Qed.
Lemma lem8026289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8026290 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term109 A M N s t) = (term110 A M N s t).
Proof. exact (MK_COMB (@lem8026289) (@lem8026288 A M N s t)). Qed.
Lemma lem8026291 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term79 A M N s t x) = (term80 A M N x s t).
Proof. exact (eq_refl (term79 A M N s t x)). Qed.
Lemma lem8026292 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026293 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (y : cart A N) : (term81 A M N s t x y) = (term82 A M N x s t y).
Proof. exact (MK_COMB (@lem8026291 A M N x s t) (@lem8026292 A N y)). Qed.
Lemma lem8026294 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term82 A M N x s t y) = (term24 A M N x s y t).
Proof. exact (eq_refl (term82 A M N x s t y)). Qed.
Lemma lem8026295 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term81 A M N s t x y) = (term24 A M N x s y t).
Proof. exact (TRANS (@lem8026293 A M N x s t y) (@lem8026294 A M N x s y t)). Qed.
Lemma lem8026296 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8026297 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term111 A M N s t x y) = (term112 A M N x s y t).
Proof. exact (MK_COMB (@lem8026296) (@lem8026295 A M N x s y t)). Qed.
Lemma lem8026298 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term113 A M N s t x y) = (term114 A M N s t x y).
Proof. exact (eq_refl (term113 A M N s t x y)). Qed.
Lemma lem8026299 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term115 A M N s t x y) = (term116 A M N s t x y).
Proof. exact (MK_COMB (@lem8026297 A M N x s y t) (@lem8026298 A M N s t x y)). Qed.
Lemma lem8026300 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term117 A M N s t x) = (term118 A M N s t x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026299 A M N s t x y)). Qed.
Lemma lem8026301 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026302 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term119 A M N s t x) = (term120 A M N s t x).
Proof. exact (MK_COMB (@lem8026301 A N) (@lem8026300 A M N s t x)). Qed.
Lemma lem8026303 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term121 A M N s t) = (term122 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8026302 A M N s t x)). Qed.
Lemma lem8026304 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026305 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term76 A M N s t) = (term123 A M N s t).
Proof. exact (MK_COMB (@lem8026304 A M) (@lem8026303 A M N s t)). Qed.
Lemma lem8026306 {A M N : Type'} (s : type24 A M) (t : type24 A N) : ((term75 A M N s t) = (term76 A M N s t)) = ((term108 A M N s t) = (term123 A M N s t)).
Proof. exact (MK_COMB (@lem8026290 A M N s t) (@lem8026305 A M N s t)). Qed.
Lemma lem8026307 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term108 A M N s t) = (term123 A M N s t).
Proof. exact (EQ_MP (@lem8026306 A M N s t) (@lem8026261 A M N s t)). Qed.
Lemma lem8026322 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a0 = (term124 A M N a0 a1).
Proof. exact (@lem51128 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026323 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (@lem8026322 A M N x y). Qed.
Lemma lem8026324 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a1 = (term125 A M N a0 a1).
Proof. exact (@lem51159 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026325 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (@lem8026324 A M N x y). Qed.
Lemma lem8026326 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8026327 {A M : Type'} : (term126 A M) = (term126 A M).
Proof. exact (eq_refl (term126 A M)). Qed.
Lemma lem8026328 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A M x) = (term128 A M N x y).
Proof. exact (MK_COMB (@lem8026327 A M) (@lem8026323 A M N x y)). Qed.
Lemma lem8026329 {A M N : Type'} (x : cart A M) (y : cart A N) : (term128 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term128 A M N x y)). Qed.
Lemma lem8026330 {A M : Type'} (x : cart A M) : (term129 A M x) = (term129 A M x).
Proof. exact (eq_refl (term129 A M x)). Qed.
Lemma lem8026331 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = ((term127 A M x) = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026330 A M x) (@lem8026329 A M N x y)). Qed.
Lemma lem8026332 {A M : Type'} (x : cart A M) : (term127 A M x) = x.
Proof. exact (eq_refl (term127 A M x)). Qed.
Lemma lem8026333 {A M : Type'} : (@eq (cart A M)) = (@eq (cart A M)).
Proof. exact (eq_refl (@eq (cart A M))). Qed.
Lemma lem8026334 {A M : Type'} (x : cart A M) : (term129 A M x) = (@eq (cart A M) x).
Proof. exact (MK_COMB (@lem8026333 A M) (@lem8026332 A M x)). Qed.
Lemma lem8026335 {A M N : Type'} (x : cart A M) (y : cart A N) : (term124 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term124 A M N x y)). Qed.
Lemma lem8026336 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term124 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026334 A M x) (@lem8026335 A M N x y)). Qed.
Lemma lem8026337 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (TRANS (@lem8026331 A M N x y) (@lem8026336 A M N x y)). Qed.
Lemma lem8026338 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026337 A M N x y) (@lem8026328 A M N x y)). Qed.
Lemma lem8026339 {A M : Type'} (x : cart A M) : (@eq (cart A M) x) = (@eq (cart A M) x).
Proof. exact (eq_refl (@eq (cart A M) x)). Qed.
Lemma lem8026340 {A M N : Type'} (x : cart A M) (y : cart A N) : (x = x) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026339 A M x) (@lem8026338 A M N x y)). Qed.
Lemma lem8026341 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026340 A M N x y) (@lem8026326 A M x)). Qed.
Lemma lem8026342 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026343 {A N : Type'} : (term126 A N) = (term126 A N).
Proof. exact (eq_refl (term126 A N)). Qed.
Lemma lem8026344 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A N y) = (term130 A M N x y).
Proof. exact (MK_COMB (@lem8026343 A N) (@lem8026325 A M N x y)). Qed.
Lemma lem8026345 {A M N : Type'} (x : cart A M) (y : cart A N) : (term130 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term130 A M N x y)). Qed.
Lemma lem8026346 {A N : Type'} (y : cart A N) : (term129 A N y) = (term129 A N y).
Proof. exact (eq_refl (term129 A N y)). Qed.
Lemma lem8026347 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = ((term127 A N y) = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026346 A N y) (@lem8026345 A M N x y)). Qed.
Lemma lem8026348 {A N : Type'} (y : cart A N) : (term127 A N y) = y.
Proof. exact (eq_refl (term127 A N y)). Qed.
Lemma lem8026349 {A N : Type'} : (@eq (cart A N)) = (@eq (cart A N)).
Proof. exact (eq_refl (@eq (cart A N))). Qed.
Lemma lem8026350 {A N : Type'} (y : cart A N) : (term129 A N y) = (@eq (cart A N) y).
Proof. exact (MK_COMB (@lem8026349 A N) (@lem8026348 A N y)). Qed.
Lemma lem8026351 {A M N : Type'} (x : cart A M) (y : cart A N) : (term125 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term125 A M N x y)). Qed.
Lemma lem8026352 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term125 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026350 A N y) (@lem8026351 A M N x y)). Qed.
Lemma lem8026353 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (TRANS (@lem8026347 A M N x y) (@lem8026352 A M N x y)). Qed.
Lemma lem8026354 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026353 A M N x y) (@lem8026344 A M N x y)). Qed.
Lemma lem8026355 {A N : Type'} (y : cart A N) : (@eq (cart A N) y) = (@eq (cart A N) y).
Proof. exact (eq_refl (@eq (cart A N) y)). Qed.
Lemma lem8026356 {A M N : Type'} (x : cart A M) (y : cart A N) : (y = y) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026355 A N y) (@lem8026354 A M N x y)). Qed.
Lemma lem8026357 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026356 A M N x y) (@lem8026342 A N y)). Qed.
Lemma lem8026358 {A M N : Type'} : (term131 A M N) = (term131 A M N).
Proof. exact (eq_refl (term131 A M N)). Qed.
Lemma lem8026359 {A M N : Type'} (x : cart A M) (y : cart A N) : (term132 A M N x) = (term133 A M N x y).
Proof. exact (MK_COMB (@lem8026358 A M N) (@lem8026341 A M N x y)). Qed.
Lemma lem8026360 {A M N : Type'} (x : cart A M) (y : cart A N) : (term133 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term133 A M N x y)). Qed.
Lemma lem8026361 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term135 A M N x).
Proof. exact (eq_refl (term135 A M N x)). Qed.
Lemma lem8026362 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term132 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026361 A M N x) (@lem8026360 A M N x y)). Qed.
Lemma lem8026363 {A M N : Type'} (x : cart A M) : (term132 A M N x) = (term136 A M N x).
Proof. exact (eq_refl (term132 A M N x)). Qed.
Lemma lem8026364 {A M N : Type'} : (@eq ((cart A N) -> cart A (finite_sum M N))) = (@eq ((cart A N) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq ((cart A N) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026365 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term137 A M N x).
Proof. exact (MK_COMB (@lem8026364 A M N) (@lem8026363 A M N x)). Qed.
Lemma lem8026366 {A M N : Type'} (x : cart A M) (y : cart A N) : (term134 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term134 A M N x y)). Qed.
Lemma lem8026367 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term134 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026365 A M N x) (@lem8026366 A M N x y)). Qed.
Lemma lem8026368 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (TRANS (@lem8026362 A M N x y) (@lem8026367 A M N x y)). Qed.
Lemma lem8026369 {A M N : Type'} (x : cart A M) (y : cart A N) : (term136 A M N x) = (term134 A M N x y).
Proof. exact (EQ_MP (@lem8026368 A M N x y) (@lem8026359 A M N x y)). Qed.
Lemma lem8026370 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (term139 A M N x y).
Proof. exact (MK_COMB (@lem8026369 A M N x y) (@lem8026357 A M N x y)). Qed.
Lemma lem8026371 {A M N : Type'} (x : cart A M) (y : cart A N) : (term139 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term139 A M N x y)). Qed.
Lemma lem8026372 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term141 A M N x y).
Proof. exact (eq_refl (term141 A M N x y)). Qed.
Lemma lem8026373 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((term138 A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026372 A M N x y) (@lem8026371 A M N x y)). Qed.
Lemma lem8026374 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (@pastecart A M N x y).
Proof. exact (eq_refl (term138 A M N x y)). Qed.
Lemma lem8026375 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026376 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term142 A M N x y).
Proof. exact (MK_COMB (@lem8026375 A M N) (@lem8026374 A M N x y)). Qed.
Lemma lem8026377 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term140 A M N x y)). Qed.
Lemma lem8026378 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term140 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026376 A M N x y) (@lem8026377 A M N x y)). Qed.
Lemma lem8026379 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (TRANS (@lem8026373 A M N x y) (@lem8026378 A M N x y)). Qed.
Lemma lem8026380 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term140 A M N x y).
Proof. exact (EQ_MP (@lem8026379 A M N x y) (@lem8026370 A M N x y)). Qed.
Lemma lem8026381 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (@pastecart A M N x y).
Proof. exact (SYM (@lem8026380 A M N x y)). Qed.
Lemma lem8026382 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term143 A M N x y)). Qed.
Lemma lem8026383 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (@pastecart A M N x y).
Proof. exact (TRANS (@lem8026382 A M N x y) (@lem8026381 A M N x y)). Qed.
Lemma lem8026384 {A M N : Type'} (x : cart A M) : term144 A M N x.
Proof. exact (fun y : cart A N => @lem8026383 A M N x y). Qed.
Lemma lem8026385 {A M N : Type'} : term145 A M N.
Proof. exact (fun x : cart A M => @lem8026384 A M N x). Qed.
Lemma lem8026386 {A M N : Type'} : term146 A M N.
Proof. exact (ex_intro (term147 A M N) (term148 A M N) (@lem8026385 A M N)). Qed.
Lemma lem8026388 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8026389 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (a = b) = (@GEQ (cart A (finite_sum M N)) a b).
Proof. exact (@lem8026388 (type2 A M N) a b). Qed.
Lemma lem8026390 {A M N : Type'} (_105927 : type1162 A M N) (x : cart A M) (y : cart A N) : ((term149 A M N _105927 x y) = (@pastecart A M N x y)) = (term150 A M N _105927 x y).
Proof. exact (@lem8026389 A M N (term149 A M N _105927 x y) (@pastecart A M N x y)). Qed.
Lemma lem8026391 {A M N : Type'} (_105927 : type1162 A M N) (x : cart A M) : (term151 A M N _105927 x) = (term152 A M N _105927 x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026390 A M N _105927 x y)). Qed.
Lemma lem8026392 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026393 {A M N : Type'} (_105927 : type1162 A M N) (x : cart A M) : (term153 A M N _105927 x) = (term154 A M N _105927 x).
Proof. exact (MK_COMB (@lem8026392 A N) (@lem8026391 A M N _105927 x)). Qed.
Lemma lem8026394 {A M N : Type'} (_105927 : type1162 A M N) : (term155 A M N _105927) = (term156 A M N _105927).
Proof. exact (fun_ext (fun x : cart A M => @lem8026393 A M N _105927 x)). Qed.
Lemma lem8026395 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026396 {A M N : Type'} (_105927 : type1162 A M N) : (term157 A M N _105927) = (term158 A M N _105927).
Proof. exact (MK_COMB (@lem8026395 A M) (@lem8026394 A M N _105927)). Qed.
Lemma lem8026397 {A M N : Type'} : (term147 A M N) = (term159 A M N).
Proof. exact (fun_ext (fun _105927 : type1162 A M N => @lem8026396 A M N _105927)). Qed.
Lemma lem8026398 {A M N : Type'} : (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))) = (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026399 {A M N : Type'} : (term146 A M N) = (term160 A M N).
Proof. exact (MK_COMB (@lem8026398 A M N) (@lem8026397 A M N)). Qed.
Lemma lem8026400 {A M N : Type'} : term160 A M N.
Proof. exact (EQ_MP (@lem8026399 A M N) (@lem8026386 A M N)). Qed.
Lemma lem8026402 {_5076 : Type'} (P : _5076 -> Prop) : term161 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8026403 {A M N : Type'} (P : type280 A M N) : term162 A M N P.
Proof. exact (@lem8026402 (type1162 A M N) P). Qed.
Lemma lem8026404 {A M N : Type'} : term163 A M N.
Proof. exact (@lem8026403 A M N (term159 A M N)). Qed.
Lemma lem8026405 {A M N : Type'} : term164 A M N.
Proof. exact (@lem8026404 A M N (@lem8026400 A M N)). Qed.
Lemma lem8026406 {A M N : Type'} : (term164 A M N) = (term165 A M N).
Proof. exact (eq_refl (term164 A M N)). Qed.
Lemma lem8026407 {A M N : Type'} : term165 A M N.
Proof. exact (EQ_MP (@lem8026406 A M N) (@lem8026405 A M N)). Qed.
Lemma lem8026408 {A M N : Type'} (x : cart A M) : term166 A M N x.
Proof. exact (@lem8026407 A M N x). Qed.
Lemma lem8026409 {A M N : Type'} (x : cart A M) : (term166 A M N x) = (term167 A M N x).
Proof. exact (eq_refl (term166 A M N x)). Qed.
Lemma lem8026410 {A M N : Type'} (x : cart A M) : term167 A M N x.
Proof. exact (EQ_MP (@lem8026409 A M N x) (@lem8026408 A M N x)). Qed.
Lemma lem8026411 {A M N : Type'} (x : cart A M) (y : cart A N) : term168 A M N x y.
Proof. exact (@lem8026410 A M N x y). Qed.
Lemma lem8026412 {A M N : Type'} (x : cart A M) (y : cart A N) : (term168 A M N x y) = (term169 A M N x y).
Proof. exact (eq_refl (term168 A M N x y)). Qed.
Lemma lem8026413 {A M N : Type'} (x : cart A M) (y : cart A N) : term169 A M N x y.
Proof. exact (EQ_MP (@lem8026412 A M N x y) (@lem8026411 A M N x y)). Qed.
Lemma lem8026415 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8026416 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (@GEQ (cart A (finite_sum M N)) a b) = (a = b).
Proof. exact (@lem8026415 (type2 A M N) a b). Qed.
Lemma lem8026417 {A M N : Type'} (x : cart A M) (y : cart A N) : (term169 A M N x y) = ((term170 A M N x y) = (@pastecart A M N x y)).
Proof. exact (@lem8026416 A M N (term170 A M N x y) (@pastecart A M N x y)). Qed.
Lemma lem8026418 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (EQ_MP (@lem8026417 A M N x y) (@lem8026413 A M N x y)). Qed.
Lemma lem8026419 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (@lem8026418 A M N x y). Qed.
Lemma lem8026420 {A M N : Type'} : (@IN (cart A (finite_sum M N))) = (@IN (cart A (finite_sum M N))).
Proof. exact (eq_refl (@IN (cart A (finite_sum M N)))). Qed.
Lemma lem8026421 {A M N : Type'} (x : cart A M) (y : cart A N) : (term171 A M N x y) = (term172 A M N x y).
Proof. exact (MK_COMB (@lem8026420 A M N) (@lem8026419 A M N x y)). Qed.
Lemma lem8026422 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (@PCROSS A M N s t).
Proof. exact (eq_refl (@PCROSS A M N s t)). Qed.
Lemma lem8026423 {A M N : Type'} (x : cart A M) (y : cart A N) (s : type24 A M) (t : type24 A N) : (term173 A M N x y s t) = (term23 A M N x y s t).
Proof. exact (MK_COMB (@lem8026421 A M N x y) (@lem8026422 A M N s t)). Qed.
Lemma lem8026425 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term23 _141927 _141928 _141929 x y s t) = (term24 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8026158 _141927 _141928 _141929 x s y t) (@lem8026157 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8026426 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term23 A M N x y s t) = (term24 A M N x s y t).
Proof. exact (@lem8026425 A M N x s y t). Qed.
Lemma lem8026429 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term173 A M N x y s t) = (term24 A M N x s y t).
Proof. exact (TRANS (@lem8026423 A M N x y s t) (@lem8026426 A M N x s y t)). Qed.
Lemma lem8026430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8026431 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term174 A M N x y s t) = (term175 A M N x s y t).
Proof. exact (MK_COMB (@lem8026430) (@lem8026429 A M N x s y t)). Qed.
Lemma lem8026435 {A B : Type'} (f : A -> B) (y : A) : (term176 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8026436 {A M N : Type'} (f : type15 A M N) (y : type2 A M N) : (term177 A M N f y) = (f y).
Proof. exact (@lem8026435 (type2 A M N) (type1642 A M N) f y). Qed.
Lemma lem8026437 {A M N : Type'} (x : cart A M) (y : cart A N) : (term178 A M N x y) = (term179 A M N x y).
Proof. exact (@lem8026436 A M N (term180 A M N) (term170 A M N x y)). Qed.
Lemma lem8026438 {A M N : Type'} (z : type2 A M N) : (term181 A M N z) = (term182 A M N z).
Proof. exact (eq_refl (term181 A M N z)). Qed.
Lemma lem8026439 {A M N : Type'} : (term183 A M N) = (term180 A M N).
Proof. exact (fun_ext (fun z : type2 A M N => @lem8026438 A M N z)). Qed.
Lemma lem8026440 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (term170 A M N x y).
Proof. exact (eq_refl (term170 A M N x y)). Qed.
Lemma lem8026441 {A M N : Type'} (x : cart A M) (y : cart A N) : (term178 A M N x y) = (term179 A M N x y).
Proof. exact (MK_COMB (@lem8026439 A M N) (@lem8026440 A M N x y)). Qed.
Lemma lem8026442 {A M N : Type'} : (@eq (prod (cart A M) (cart A N))) = (@eq (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@eq (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026443 {A M N : Type'} (x : cart A M) (y : cart A N) : (term184 A M N x y) = (term185 A M N x y).
Proof. exact (MK_COMB (@lem8026442 A M N) (@lem8026441 A M N x y)). Qed.
Lemma lem8026444 {A M N : Type'} (x : cart A M) (y : cart A N) : (term179 A M N x y) = (term186 A M N x y).
Proof. exact (eq_refl (term179 A M N x y)). Qed.
Lemma lem8026445 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term178 A M N x y) = (term179 A M N x y)) = ((term179 A M N x y) = (term186 A M N x y)).
Proof. exact (MK_COMB (@lem8026443 A M N x y) (@lem8026444 A M N x y)). Qed.
Lemma lem8026446 {A M N : Type'} (x : cart A M) (y : cart A N) : (term179 A M N x y) = (term186 A M N x y).
Proof. exact (EQ_MP (@lem8026445 A M N x y) (@lem8026437 A M N x y)). Qed.
Lemma lem8026447 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a0 = (term124 A M N a0 a1).
Proof. exact (@lem51128 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026448 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (@lem8026447 A M N x y). Qed.
Lemma lem8026449 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a1 = (term125 A M N a0 a1).
Proof. exact (@lem51159 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026450 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (@lem8026449 A M N x y). Qed.
Lemma lem8026451 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8026452 {A M : Type'} : (term126 A M) = (term126 A M).
Proof. exact (eq_refl (term126 A M)). Qed.
Lemma lem8026453 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A M x) = (term128 A M N x y).
Proof. exact (MK_COMB (@lem8026452 A M) (@lem8026448 A M N x y)). Qed.
Lemma lem8026454 {A M N : Type'} (x : cart A M) (y : cart A N) : (term128 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term128 A M N x y)). Qed.
Lemma lem8026455 {A M : Type'} (x : cart A M) : (term129 A M x) = (term129 A M x).
Proof. exact (eq_refl (term129 A M x)). Qed.
Lemma lem8026456 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = ((term127 A M x) = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026455 A M x) (@lem8026454 A M N x y)). Qed.
Lemma lem8026457 {A M : Type'} (x : cart A M) : (term127 A M x) = x.
Proof. exact (eq_refl (term127 A M x)). Qed.
Lemma lem8026458 {A M : Type'} : (@eq (cart A M)) = (@eq (cart A M)).
Proof. exact (eq_refl (@eq (cart A M))). Qed.
Lemma lem8026459 {A M : Type'} (x : cart A M) : (term129 A M x) = (@eq (cart A M) x).
Proof. exact (MK_COMB (@lem8026458 A M) (@lem8026457 A M x)). Qed.
Lemma lem8026460 {A M N : Type'} (x : cart A M) (y : cart A N) : (term124 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term124 A M N x y)). Qed.
Lemma lem8026461 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term124 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026459 A M x) (@lem8026460 A M N x y)). Qed.
Lemma lem8026462 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (TRANS (@lem8026456 A M N x y) (@lem8026461 A M N x y)). Qed.
Lemma lem8026463 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026462 A M N x y) (@lem8026453 A M N x y)). Qed.
Lemma lem8026464 {A M : Type'} (x : cart A M) : (@eq (cart A M) x) = (@eq (cart A M) x).
Proof. exact (eq_refl (@eq (cart A M) x)). Qed.
Lemma lem8026465 {A M N : Type'} (x : cart A M) (y : cart A N) : (x = x) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026464 A M x) (@lem8026463 A M N x y)). Qed.
Lemma lem8026466 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026465 A M N x y) (@lem8026451 A M x)). Qed.
Lemma lem8026467 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026468 {A N : Type'} : (term126 A N) = (term126 A N).
Proof. exact (eq_refl (term126 A N)). Qed.
Lemma lem8026469 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A N y) = (term130 A M N x y).
Proof. exact (MK_COMB (@lem8026468 A N) (@lem8026450 A M N x y)). Qed.
Lemma lem8026470 {A M N : Type'} (x : cart A M) (y : cart A N) : (term130 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term130 A M N x y)). Qed.
Lemma lem8026471 {A N : Type'} (y : cart A N) : (term129 A N y) = (term129 A N y).
Proof. exact (eq_refl (term129 A N y)). Qed.
Lemma lem8026472 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = ((term127 A N y) = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026471 A N y) (@lem8026470 A M N x y)). Qed.
Lemma lem8026473 {A N : Type'} (y : cart A N) : (term127 A N y) = y.
Proof. exact (eq_refl (term127 A N y)). Qed.
Lemma lem8026474 {A N : Type'} : (@eq (cart A N)) = (@eq (cart A N)).
Proof. exact (eq_refl (@eq (cart A N))). Qed.
Lemma lem8026475 {A N : Type'} (y : cart A N) : (term129 A N y) = (@eq (cart A N) y).
Proof. exact (MK_COMB (@lem8026474 A N) (@lem8026473 A N y)). Qed.
Lemma lem8026476 {A M N : Type'} (x : cart A M) (y : cart A N) : (term125 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term125 A M N x y)). Qed.
Lemma lem8026477 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term125 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026475 A N y) (@lem8026476 A M N x y)). Qed.
Lemma lem8026478 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (TRANS (@lem8026472 A M N x y) (@lem8026477 A M N x y)). Qed.
Lemma lem8026479 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026478 A M N x y) (@lem8026469 A M N x y)). Qed.
Lemma lem8026480 {A N : Type'} (y : cart A N) : (@eq (cart A N) y) = (@eq (cart A N) y).
Proof. exact (eq_refl (@eq (cart A N) y)). Qed.
Lemma lem8026481 {A M N : Type'} (x : cart A M) (y : cart A N) : (y = y) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026480 A N y) (@lem8026479 A M N x y)). Qed.
Lemma lem8026482 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026481 A M N x y) (@lem8026467 A N y)). Qed.
Lemma lem8026483 {A M N : Type'} : (term131 A M N) = (term131 A M N).
Proof. exact (eq_refl (term131 A M N)). Qed.
Lemma lem8026484 {A M N : Type'} (x : cart A M) (y : cart A N) : (term132 A M N x) = (term133 A M N x y).
Proof. exact (MK_COMB (@lem8026483 A M N) (@lem8026466 A M N x y)). Qed.
Lemma lem8026485 {A M N : Type'} (x : cart A M) (y : cart A N) : (term133 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term133 A M N x y)). Qed.
Lemma lem8026486 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term135 A M N x).
Proof. exact (eq_refl (term135 A M N x)). Qed.
Lemma lem8026487 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term132 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026486 A M N x) (@lem8026485 A M N x y)). Qed.
Lemma lem8026488 {A M N : Type'} (x : cart A M) : (term132 A M N x) = (term136 A M N x).
Proof. exact (eq_refl (term132 A M N x)). Qed.
Lemma lem8026489 {A M N : Type'} : (@eq ((cart A N) -> cart A (finite_sum M N))) = (@eq ((cart A N) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq ((cart A N) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026490 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term137 A M N x).
Proof. exact (MK_COMB (@lem8026489 A M N) (@lem8026488 A M N x)). Qed.
Lemma lem8026491 {A M N : Type'} (x : cart A M) (y : cart A N) : (term134 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term134 A M N x y)). Qed.
Lemma lem8026492 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term134 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026490 A M N x) (@lem8026491 A M N x y)). Qed.
Lemma lem8026493 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (TRANS (@lem8026487 A M N x y) (@lem8026492 A M N x y)). Qed.
Lemma lem8026494 {A M N : Type'} (x : cart A M) (y : cart A N) : (term136 A M N x) = (term134 A M N x y).
Proof. exact (EQ_MP (@lem8026493 A M N x y) (@lem8026484 A M N x y)). Qed.
Lemma lem8026495 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (term139 A M N x y).
Proof. exact (MK_COMB (@lem8026494 A M N x y) (@lem8026482 A M N x y)). Qed.
Lemma lem8026496 {A M N : Type'} (x : cart A M) (y : cart A N) : (term139 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term139 A M N x y)). Qed.
Lemma lem8026497 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term141 A M N x y).
Proof. exact (eq_refl (term141 A M N x y)). Qed.
Lemma lem8026498 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((term138 A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026497 A M N x y) (@lem8026496 A M N x y)). Qed.
Lemma lem8026499 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (@pastecart A M N x y).
Proof. exact (eq_refl (term138 A M N x y)). Qed.
Lemma lem8026500 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026501 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term142 A M N x y).
Proof. exact (MK_COMB (@lem8026500 A M N) (@lem8026499 A M N x y)). Qed.
Lemma lem8026502 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term140 A M N x y)). Qed.
Lemma lem8026503 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term140 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026501 A M N x y) (@lem8026502 A M N x y)). Qed.
Lemma lem8026504 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (TRANS (@lem8026498 A M N x y) (@lem8026503 A M N x y)). Qed.
Lemma lem8026505 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term140 A M N x y).
Proof. exact (EQ_MP (@lem8026504 A M N x y) (@lem8026495 A M N x y)). Qed.
Lemma lem8026506 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (@pastecart A M N x y).
Proof. exact (SYM (@lem8026505 A M N x y)). Qed.
Lemma lem8026507 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term143 A M N x y)). Qed.
Lemma lem8026508 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (@pastecart A M N x y).
Proof. exact (TRANS (@lem8026507 A M N x y) (@lem8026506 A M N x y)). Qed.
Lemma lem8026509 {A M N : Type'} (x : cart A M) : term144 A M N x.
Proof. exact (fun y : cart A N => @lem8026508 A M N x y). Qed.
Lemma lem8026510 {A M N : Type'} : term145 A M N.
Proof. exact (fun x : cart A M => @lem8026509 A M N x). Qed.
Lemma lem8026511 {A M N : Type'} : term146 A M N.
Proof. exact (ex_intro (term147 A M N) (term148 A M N) (@lem8026510 A M N)). Qed.
Lemma lem8026513 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8026514 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (a = b) = (@GEQ (cart A (finite_sum M N)) a b).
Proof. exact (@lem8026513 (type2 A M N) a b). Qed.
Lemma lem8026515 {A M N : Type'} (_105939 : type1162 A M N) (x : cart A M) (y : cart A N) : ((term149 A M N _105939 x y) = (@pastecart A M N x y)) = (term150 A M N _105939 x y).
Proof. exact (@lem8026514 A M N (term149 A M N _105939 x y) (@pastecart A M N x y)). Qed.
Lemma lem8026516 {A M N : Type'} (_105939 : type1162 A M N) (x : cart A M) : (term151 A M N _105939 x) = (term152 A M N _105939 x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026515 A M N _105939 x y)). Qed.
Lemma lem8026517 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026518 {A M N : Type'} (_105939 : type1162 A M N) (x : cart A M) : (term153 A M N _105939 x) = (term154 A M N _105939 x).
Proof. exact (MK_COMB (@lem8026517 A N) (@lem8026516 A M N _105939 x)). Qed.
Lemma lem8026519 {A M N : Type'} (_105939 : type1162 A M N) : (term155 A M N _105939) = (term156 A M N _105939).
Proof. exact (fun_ext (fun x : cart A M => @lem8026518 A M N _105939 x)). Qed.
Lemma lem8026520 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026521 {A M N : Type'} (_105939 : type1162 A M N) : (term157 A M N _105939) = (term158 A M N _105939).
Proof. exact (MK_COMB (@lem8026520 A M) (@lem8026519 A M N _105939)). Qed.
Lemma lem8026522 {A M N : Type'} : (term147 A M N) = (term159 A M N).
Proof. exact (fun_ext (fun _105939 : type1162 A M N => @lem8026521 A M N _105939)). Qed.
Lemma lem8026523 {A M N : Type'} : (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))) = (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026524 {A M N : Type'} : (term146 A M N) = (term160 A M N).
Proof. exact (MK_COMB (@lem8026523 A M N) (@lem8026522 A M N)). Qed.
Lemma lem8026525 {A M N : Type'} : term160 A M N.
Proof. exact (EQ_MP (@lem8026524 A M N) (@lem8026511 A M N)). Qed.
Lemma lem8026527 {_5076 : Type'} (P : _5076 -> Prop) : term161 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8026528 {A M N : Type'} (P : type280 A M N) : term162 A M N P.
Proof. exact (@lem8026527 (type1162 A M N) P). Qed.
Lemma lem8026529 {A M N : Type'} : term163 A M N.
Proof. exact (@lem8026528 A M N (term159 A M N)). Qed.
Lemma lem8026530 {A M N : Type'} : term164 A M N.
Proof. exact (@lem8026529 A M N (@lem8026525 A M N)). Qed.
Lemma lem8026531 {A M N : Type'} : (term164 A M N) = (term165 A M N).
Proof. exact (eq_refl (term164 A M N)). Qed.
Lemma lem8026532 {A M N : Type'} : term165 A M N.
Proof. exact (EQ_MP (@lem8026531 A M N) (@lem8026530 A M N)). Qed.
Lemma lem8026533 {A M N : Type'} (x : cart A M) : term166 A M N x.
Proof. exact (@lem8026532 A M N x). Qed.
Lemma lem8026534 {A M N : Type'} (x : cart A M) : (term166 A M N x) = (term167 A M N x).
Proof. exact (eq_refl (term166 A M N x)). Qed.
Lemma lem8026535 {A M N : Type'} (x : cart A M) : term167 A M N x.
Proof. exact (EQ_MP (@lem8026534 A M N x) (@lem8026533 A M N x)). Qed.
Lemma lem8026536 {A M N : Type'} (x : cart A M) (y : cart A N) : term168 A M N x y.
Proof. exact (@lem8026535 A M N x y). Qed.
Lemma lem8026537 {A M N : Type'} (x : cart A M) (y : cart A N) : (term168 A M N x y) = (term169 A M N x y).
Proof. exact (eq_refl (term168 A M N x y)). Qed.
Lemma lem8026538 {A M N : Type'} (x : cart A M) (y : cart A N) : term169 A M N x y.
Proof. exact (EQ_MP (@lem8026537 A M N x y) (@lem8026536 A M N x y)). Qed.
Lemma lem8026540 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8026541 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (@GEQ (cart A (finite_sum M N)) a b) = (a = b).
Proof. exact (@lem8026540 (type2 A M N) a b). Qed.
Lemma lem8026542 {A M N : Type'} (x : cart A M) (y : cart A N) : (term169 A M N x y) = ((term170 A M N x y) = (@pastecart A M N x y)).
Proof. exact (@lem8026541 A M N (term170 A M N x y) (@pastecart A M N x y)). Qed.
Lemma lem8026543 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (EQ_MP (@lem8026542 A M N x y) (@lem8026538 A M N x y)). Qed.
Lemma lem8026544 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (@lem8026543 A M N x y). Qed.
Lemma lem8026545 {A M N : Type'} : (@fstcart A M N) = (@fstcart A M N).
Proof. exact (eq_refl (@fstcart A M N)). Qed.
Lemma lem8026546 {A M N : Type'} (x : cart A M) (y : cart A N) : (term187 A M N x y) = (term7 A M N x y).
Proof. exact (MK_COMB (@lem8026545 A M N) (@lem8026544 A M N x y)). Qed.
Lemma lem8026547 {A M N : Type'} : (@pair (cart A M) (cart A N)) = (@pair (cart A M) (cart A N)).
Proof. exact (eq_refl (@pair (cart A M) (cart A N))). Qed.
Lemma lem8026548 {A M N : Type'} (x : cart A M) (y : cart A N) : (term188 A M N x y) = (term189 A M N x y).
Proof. exact (MK_COMB (@lem8026547 A M N) (@lem8026546 A M N x y)). Qed.
Lemma lem8026549 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a0 = (term124 A M N a0 a1).
Proof. exact (@lem51128 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026550 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (@lem8026549 A M N x y). Qed.
Lemma lem8026551 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a1 = (term125 A M N a0 a1).
Proof. exact (@lem51159 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026552 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (@lem8026551 A M N x y). Qed.
Lemma lem8026553 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8026554 {A M : Type'} : (term126 A M) = (term126 A M).
Proof. exact (eq_refl (term126 A M)). Qed.
Lemma lem8026555 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A M x) = (term128 A M N x y).
Proof. exact (MK_COMB (@lem8026554 A M) (@lem8026550 A M N x y)). Qed.
Lemma lem8026556 {A M N : Type'} (x : cart A M) (y : cart A N) : (term128 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term128 A M N x y)). Qed.
Lemma lem8026557 {A M : Type'} (x : cart A M) : (term129 A M x) = (term129 A M x).
Proof. exact (eq_refl (term129 A M x)). Qed.
Lemma lem8026558 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = ((term127 A M x) = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026557 A M x) (@lem8026556 A M N x y)). Qed.
Lemma lem8026559 {A M : Type'} (x : cart A M) : (term127 A M x) = x.
Proof. exact (eq_refl (term127 A M x)). Qed.
Lemma lem8026560 {A M : Type'} : (@eq (cart A M)) = (@eq (cart A M)).
Proof. exact (eq_refl (@eq (cart A M))). Qed.
Lemma lem8026561 {A M : Type'} (x : cart A M) : (term129 A M x) = (@eq (cart A M) x).
Proof. exact (MK_COMB (@lem8026560 A M) (@lem8026559 A M x)). Qed.
Lemma lem8026562 {A M N : Type'} (x : cart A M) (y : cart A N) : (term124 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term124 A M N x y)). Qed.
Lemma lem8026563 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term124 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026561 A M x) (@lem8026562 A M N x y)). Qed.
Lemma lem8026564 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (TRANS (@lem8026558 A M N x y) (@lem8026563 A M N x y)). Qed.
Lemma lem8026565 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026564 A M N x y) (@lem8026555 A M N x y)). Qed.
Lemma lem8026566 {A M : Type'} (x : cart A M) : (@eq (cart A M) x) = (@eq (cart A M) x).
Proof. exact (eq_refl (@eq (cart A M) x)). Qed.
Lemma lem8026567 {A M N : Type'} (x : cart A M) (y : cart A N) : (x = x) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026566 A M x) (@lem8026565 A M N x y)). Qed.
Lemma lem8026568 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026567 A M N x y) (@lem8026553 A M x)). Qed.
Lemma lem8026569 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026570 {A N : Type'} : (term126 A N) = (term126 A N).
Proof. exact (eq_refl (term126 A N)). Qed.
Lemma lem8026571 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A N y) = (term130 A M N x y).
Proof. exact (MK_COMB (@lem8026570 A N) (@lem8026552 A M N x y)). Qed.
Lemma lem8026572 {A M N : Type'} (x : cart A M) (y : cart A N) : (term130 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term130 A M N x y)). Qed.
Lemma lem8026573 {A N : Type'} (y : cart A N) : (term129 A N y) = (term129 A N y).
Proof. exact (eq_refl (term129 A N y)). Qed.
Lemma lem8026574 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = ((term127 A N y) = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026573 A N y) (@lem8026572 A M N x y)). Qed.
Lemma lem8026575 {A N : Type'} (y : cart A N) : (term127 A N y) = y.
Proof. exact (eq_refl (term127 A N y)). Qed.
Lemma lem8026576 {A N : Type'} : (@eq (cart A N)) = (@eq (cart A N)).
Proof. exact (eq_refl (@eq (cart A N))). Qed.
Lemma lem8026577 {A N : Type'} (y : cart A N) : (term129 A N y) = (@eq (cart A N) y).
Proof. exact (MK_COMB (@lem8026576 A N) (@lem8026575 A N y)). Qed.
Lemma lem8026578 {A M N : Type'} (x : cart A M) (y : cart A N) : (term125 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term125 A M N x y)). Qed.
Lemma lem8026579 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term125 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026577 A N y) (@lem8026578 A M N x y)). Qed.
Lemma lem8026580 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (TRANS (@lem8026574 A M N x y) (@lem8026579 A M N x y)). Qed.
Lemma lem8026581 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026580 A M N x y) (@lem8026571 A M N x y)). Qed.
Lemma lem8026582 {A N : Type'} (y : cart A N) : (@eq (cart A N) y) = (@eq (cart A N) y).
Proof. exact (eq_refl (@eq (cart A N) y)). Qed.
Lemma lem8026583 {A M N : Type'} (x : cart A M) (y : cart A N) : (y = y) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026582 A N y) (@lem8026581 A M N x y)). Qed.
Lemma lem8026584 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026583 A M N x y) (@lem8026569 A N y)). Qed.
Lemma lem8026585 {A M N : Type'} : (term131 A M N) = (term131 A M N).
Proof. exact (eq_refl (term131 A M N)). Qed.
Lemma lem8026586 {A M N : Type'} (x : cart A M) (y : cart A N) : (term132 A M N x) = (term133 A M N x y).
Proof. exact (MK_COMB (@lem8026585 A M N) (@lem8026568 A M N x y)). Qed.
Lemma lem8026587 {A M N : Type'} (x : cart A M) (y : cart A N) : (term133 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term133 A M N x y)). Qed.
Lemma lem8026588 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term135 A M N x).
Proof. exact (eq_refl (term135 A M N x)). Qed.
Lemma lem8026589 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term132 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026588 A M N x) (@lem8026587 A M N x y)). Qed.
Lemma lem8026590 {A M N : Type'} (x : cart A M) : (term132 A M N x) = (term136 A M N x).
Proof. exact (eq_refl (term132 A M N x)). Qed.
Lemma lem8026591 {A M N : Type'} : (@eq ((cart A N) -> cart A (finite_sum M N))) = (@eq ((cart A N) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq ((cart A N) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026592 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term137 A M N x).
Proof. exact (MK_COMB (@lem8026591 A M N) (@lem8026590 A M N x)). Qed.
Lemma lem8026593 {A M N : Type'} (x : cart A M) (y : cart A N) : (term134 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term134 A M N x y)). Qed.
Lemma lem8026594 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term134 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026592 A M N x) (@lem8026593 A M N x y)). Qed.
Lemma lem8026595 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (TRANS (@lem8026589 A M N x y) (@lem8026594 A M N x y)). Qed.
Lemma lem8026596 {A M N : Type'} (x : cart A M) (y : cart A N) : (term136 A M N x) = (term134 A M N x y).
Proof. exact (EQ_MP (@lem8026595 A M N x y) (@lem8026586 A M N x y)). Qed.
Lemma lem8026597 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (term139 A M N x y).
Proof. exact (MK_COMB (@lem8026596 A M N x y) (@lem8026584 A M N x y)). Qed.
Lemma lem8026598 {A M N : Type'} (x : cart A M) (y : cart A N) : (term139 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term139 A M N x y)). Qed.
Lemma lem8026599 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term141 A M N x y).
Proof. exact (eq_refl (term141 A M N x y)). Qed.
Lemma lem8026600 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((term138 A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026599 A M N x y) (@lem8026598 A M N x y)). Qed.
Lemma lem8026601 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (@pastecart A M N x y).
Proof. exact (eq_refl (term138 A M N x y)). Qed.
Lemma lem8026602 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026603 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term142 A M N x y).
Proof. exact (MK_COMB (@lem8026602 A M N) (@lem8026601 A M N x y)). Qed.
Lemma lem8026604 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term140 A M N x y)). Qed.
Lemma lem8026605 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term140 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026603 A M N x y) (@lem8026604 A M N x y)). Qed.
Lemma lem8026606 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (TRANS (@lem8026600 A M N x y) (@lem8026605 A M N x y)). Qed.
Lemma lem8026607 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term140 A M N x y).
Proof. exact (EQ_MP (@lem8026606 A M N x y) (@lem8026597 A M N x y)). Qed.
Lemma lem8026608 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (@pastecart A M N x y).
Proof. exact (SYM (@lem8026607 A M N x y)). Qed.
Lemma lem8026609 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term143 A M N x y)). Qed.
Lemma lem8026610 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (@pastecart A M N x y).
Proof. exact (TRANS (@lem8026609 A M N x y) (@lem8026608 A M N x y)). Qed.
Lemma lem8026611 {A M N : Type'} (x : cart A M) : term144 A M N x.
Proof. exact (fun y : cart A N => @lem8026610 A M N x y). Qed.
Lemma lem8026612 {A M N : Type'} : term145 A M N.
Proof. exact (fun x : cart A M => @lem8026611 A M N x). Qed.
Lemma lem8026613 {A M N : Type'} : term146 A M N.
Proof. exact (ex_intro (term147 A M N) (term148 A M N) (@lem8026612 A M N)). Qed.
Lemma lem8026615 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8026616 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (a = b) = (@GEQ (cart A (finite_sum M N)) a b).
Proof. exact (@lem8026615 (type2 A M N) a b). Qed.
Lemma lem8026617 {A M N : Type'} (_105951 : type1162 A M N) (x : cart A M) (y : cart A N) : ((term149 A M N _105951 x y) = (@pastecart A M N x y)) = (term150 A M N _105951 x y).
Proof. exact (@lem8026616 A M N (term149 A M N _105951 x y) (@pastecart A M N x y)). Qed.
Lemma lem8026618 {A M N : Type'} (_105951 : type1162 A M N) (x : cart A M) : (term151 A M N _105951 x) = (term152 A M N _105951 x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026617 A M N _105951 x y)). Qed.
Lemma lem8026619 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026620 {A M N : Type'} (_105951 : type1162 A M N) (x : cart A M) : (term153 A M N _105951 x) = (term154 A M N _105951 x).
Proof. exact (MK_COMB (@lem8026619 A N) (@lem8026618 A M N _105951 x)). Qed.
Lemma lem8026621 {A M N : Type'} (_105951 : type1162 A M N) : (term155 A M N _105951) = (term156 A M N _105951).
Proof. exact (fun_ext (fun x : cart A M => @lem8026620 A M N _105951 x)). Qed.
Lemma lem8026622 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026623 {A M N : Type'} (_105951 : type1162 A M N) : (term157 A M N _105951) = (term158 A M N _105951).
Proof. exact (MK_COMB (@lem8026622 A M) (@lem8026621 A M N _105951)). Qed.
Lemma lem8026624 {A M N : Type'} : (term147 A M N) = (term159 A M N).
Proof. exact (fun_ext (fun _105951 : type1162 A M N => @lem8026623 A M N _105951)). Qed.
Lemma lem8026625 {A M N : Type'} : (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))) = (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026626 {A M N : Type'} : (term146 A M N) = (term160 A M N).
Proof. exact (MK_COMB (@lem8026625 A M N) (@lem8026624 A M N)). Qed.
Lemma lem8026627 {A M N : Type'} : term160 A M N.
Proof. exact (EQ_MP (@lem8026626 A M N) (@lem8026613 A M N)). Qed.
Lemma lem8026629 {_5076 : Type'} (P : _5076 -> Prop) : term161 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8026630 {A M N : Type'} (P : type280 A M N) : term162 A M N P.
Proof. exact (@lem8026629 (type1162 A M N) P). Qed.
Lemma lem8026631 {A M N : Type'} : term163 A M N.
Proof. exact (@lem8026630 A M N (term159 A M N)). Qed.
Lemma lem8026632 {A M N : Type'} : term164 A M N.
Proof. exact (@lem8026631 A M N (@lem8026627 A M N)). Qed.
Lemma lem8026633 {A M N : Type'} : (term164 A M N) = (term165 A M N).
Proof. exact (eq_refl (term164 A M N)). Qed.
Lemma lem8026634 {A M N : Type'} : term165 A M N.
Proof. exact (EQ_MP (@lem8026633 A M N) (@lem8026632 A M N)). Qed.
Lemma lem8026635 {A M N : Type'} (x : cart A M) : term166 A M N x.
Proof. exact (@lem8026634 A M N x). Qed.
Lemma lem8026636 {A M N : Type'} (x : cart A M) : (term166 A M N x) = (term167 A M N x).
Proof. exact (eq_refl (term166 A M N x)). Qed.
Lemma lem8026637 {A M N : Type'} (x : cart A M) : term167 A M N x.
Proof. exact (EQ_MP (@lem8026636 A M N x) (@lem8026635 A M N x)). Qed.
Lemma lem8026638 {A M N : Type'} (x : cart A M) (y : cart A N) : term168 A M N x y.
Proof. exact (@lem8026637 A M N x y). Qed.
Lemma lem8026639 {A M N : Type'} (x : cart A M) (y : cart A N) : (term168 A M N x y) = (term169 A M N x y).
Proof. exact (eq_refl (term168 A M N x y)). Qed.
Lemma lem8026640 {A M N : Type'} (x : cart A M) (y : cart A N) : term169 A M N x y.
Proof. exact (EQ_MP (@lem8026639 A M N x y) (@lem8026638 A M N x y)). Qed.
Lemma lem8026642 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8026643 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (@GEQ (cart A (finite_sum M N)) a b) = (a = b).
Proof. exact (@lem8026642 (type2 A M N) a b). Qed.
Lemma lem8026644 {A M N : Type'} (x : cart A M) (y : cart A N) : (term169 A M N x y) = ((term170 A M N x y) = (@pastecart A M N x y)).
Proof. exact (@lem8026643 A M N (term170 A M N x y) (@pastecart A M N x y)). Qed.
Lemma lem8026645 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (EQ_MP (@lem8026644 A M N x y) (@lem8026640 A M N x y)). Qed.
Lemma lem8026646 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (@lem8026645 A M N x y). Qed.
Lemma lem8026647 {A M N : Type'} : (@sndcart A M N) = (@sndcart A M N).
Proof. exact (eq_refl (@sndcart A M N)). Qed.
Lemma lem8026648 {A M N : Type'} (x : cart A M) (y : cart A N) : (term190 A M N x y) = (term3 A M N x y).
Proof. exact (MK_COMB (@lem8026647 A M N) (@lem8026646 A M N x y)). Qed.
Lemma lem8026649 {A M N : Type'} (x : cart A M) (y : cart A N) : (term186 A M N x y) = (term191 A M N x y).
Proof. exact (MK_COMB (@lem8026548 A M N x y) (@lem8026648 A M N x y)). Qed.
Lemma lem8026650 {A M N : Type'} (x : cart A M) (y : cart A N) : (term179 A M N x y) = (term191 A M N x y).
Proof. exact (TRANS (@lem8026446 A M N x y) (@lem8026649 A M N x y)). Qed.
Lemma lem8026651 {A M N : Type'} : (@eq (prod (cart A M) (cart A N))) = (@eq (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@eq (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026652 {A M N : Type'} (x : cart A M) (y : cart A N) : (term185 A M N x y) = (term192 A M N x y).
Proof. exact (MK_COMB (@lem8026651 A M N) (@lem8026650 A M N x y)). Qed.
Lemma lem8026653 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y).
Proof. exact (eq_refl (@pair (cart A M) (cart A N) x y)). Qed.
Lemma lem8026654 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term179 A M N x y) = (@pair (cart A M) (cart A N) x y)) = ((term191 A M N x y) = (@pair (cart A M) (cart A N) x y)).
Proof. exact (MK_COMB (@lem8026652 A M N x y) (@lem8026653 A M N x y)). Qed.
Lemma lem8026657 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term114 A M N s t x y) = (term193 A M N s t x y).
Proof. exact (MK_COMB (@lem8026431 A M N x s y t) (@lem8026654 A M N x y)). Qed.
Lemma lem8026660 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term112 A M N x s y t) = (term112 A M N x s y t).
Proof. exact (eq_refl (term112 A M N x s y t)). Qed.
Lemma lem8026661 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term116 A M N s t x y) = (term194 A M N s t x y).
Proof. exact (MK_COMB (@lem8026660 A M N x s y t) (@lem8026657 A M N s t x y)). Qed.
Lemma lem8026664 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term118 A M N s t x) = (term195 A M N s t x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026661 A M N s t x y)). Qed.
Lemma lem8026665 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026666 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term120 A M N s t x) = (term196 A M N s t x).
Proof. exact (MK_COMB (@lem8026665 A N) (@lem8026664 A M N s t x)). Qed.
Lemma lem8026671 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term122 A M N s t) = (term197 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8026666 A M N s t x)). Qed.
Lemma lem8026672 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026673 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term123 A M N s t) = (term198 A M N s t).
Proof. exact (MK_COMB (@lem8026672 A M) (@lem8026671 A M N s t)). Qed.
Lemma lem8026678 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term108 A M N s t) = (term198 A M N s t).
Proof. exact (TRANS (@lem8026307 A M N s t) (@lem8026673 A M N s t)). Qed.
Lemma lem8026679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8026680 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term199 A M N s t) = (term200 A M N s t).
Proof. exact (MK_COMB (@lem8026679) (@lem8026678 A M N s t)). Qed.
Lemma lem8026690 {A B : Type'} (f : A -> B) (y : A) : (term176 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8026691 {A M N : Type'} (f : type15 A M N) (y : type2 A M N) : (term177 A M N f y) = (f y).
Proof. exact (@lem8026690 (type2 A M N) (type1642 A M N) f y). Qed.
Lemma lem8026692 {A M N : Type'} (y : type2 A M N) : (term201 A M N y) = (term181 A M N y).
Proof. exact (@lem8026691 A M N (term180 A M N) y). Qed.
Lemma lem8026693 {A M N : Type'} (z : type2 A M N) : (term181 A M N z) = (term182 A M N z).
Proof. exact (eq_refl (term181 A M N z)). Qed.
Lemma lem8026694 {A M N : Type'} : (term183 A M N) = (term180 A M N).
Proof. exact (fun_ext (fun z : type2 A M N => @lem8026693 A M N z)). Qed.
Lemma lem8026695 {A M N : Type'} (y : type2 A M N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026696 {A M N : Type'} (y : type2 A M N) : (term201 A M N y) = (term181 A M N y).
Proof. exact (MK_COMB (@lem8026694 A M N) (@lem8026695 A M N y)). Qed.
Lemma lem8026697 {A M N : Type'} : (@eq (prod (cart A M) (cart A N))) = (@eq (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@eq (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026698 {A M N : Type'} (y : type2 A M N) : (term202 A M N y) = (term203 A M N y).
Proof. exact (MK_COMB (@lem8026697 A M N) (@lem8026696 A M N y)). Qed.
Lemma lem8026699 {A M N : Type'} (y : type2 A M N) : (term181 A M N y) = (term182 A M N y).
Proof. exact (eq_refl (term181 A M N y)). Qed.
Lemma lem8026700 {A M N : Type'} (y : type2 A M N) : ((term201 A M N y) = (term181 A M N y)) = ((term181 A M N y) = (term182 A M N y)).
Proof. exact (MK_COMB (@lem8026698 A M N y) (@lem8026699 A M N y)). Qed.
Lemma lem8026701 {A M N : Type'} (y : type2 A M N) : (term181 A M N y) = (term182 A M N y).
Proof. exact (EQ_MP (@lem8026700 A M N y) (@lem8026692 A M N y)). Qed.
Lemma lem8026702 {A M N : Type'} : (@IN (prod (cart A M) (cart A N))) = (@IN (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@IN (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026703 {A M N : Type'} (y : type2 A M N) : (term204 A M N y) = (term205 A M N y).
Proof. exact (MK_COMB (@lem8026702 A M N) (@lem8026701 A M N y)). Qed.
Lemma lem8026714 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term72 A M N s t) = (term72 A M N s t).
Proof. exact (eq_refl (term72 A M N s t)). Qed.
Lemma lem8026715 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term206 A M N y s t) = (term207 A M N y s t).
Proof. exact (MK_COMB (@lem8026703 A M N y) (@lem8026714 A M N s t)). Qed.
Lemma lem8026716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8026717 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term208 A M N y s t) = (term209 A M N y s t).
Proof. exact (MK_COMB (@lem8026716) (@lem8026715 A M N y s t)). Qed.
Lemma lem8026729 {A B : Type'} (f : A -> B) (y : A) : (term176 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8026730 {A M N : Type'} (f : type15 A M N) (y : type2 A M N) : (term177 A M N f y) = (f y).
Proof. exact (@lem8026729 (type2 A M N) (type1642 A M N) f y). Qed.
Lemma lem8026731 {A M N : Type'} (y : type2 A M N) : (term201 A M N y) = (term181 A M N y).
Proof. exact (@lem8026730 A M N (term180 A M N) y). Qed.
Lemma lem8026732 {A M N : Type'} (z : type2 A M N) : (term181 A M N z) = (term182 A M N z).
Proof. exact (eq_refl (term181 A M N z)). Qed.
Lemma lem8026733 {A M N : Type'} : (term183 A M N) = (term180 A M N).
Proof. exact (fun_ext (fun z : type2 A M N => @lem8026732 A M N z)). Qed.
Lemma lem8026734 {A M N : Type'} (y : type2 A M N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026735 {A M N : Type'} (y : type2 A M N) : (term201 A M N y) = (term181 A M N y).
Proof. exact (MK_COMB (@lem8026733 A M N) (@lem8026734 A M N y)). Qed.
Lemma lem8026736 {A M N : Type'} : (@eq (prod (cart A M) (cart A N))) = (@eq (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@eq (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026737 {A M N : Type'} (y : type2 A M N) : (term202 A M N y) = (term203 A M N y).
Proof. exact (MK_COMB (@lem8026736 A M N) (@lem8026735 A M N y)). Qed.
Lemma lem8026738 {A M N : Type'} (y : type2 A M N) : (term181 A M N y) = (term182 A M N y).
Proof. exact (eq_refl (term181 A M N y)). Qed.
Lemma lem8026739 {A M N : Type'} (y : type2 A M N) : ((term201 A M N y) = (term181 A M N y)) = ((term181 A M N y) = (term182 A M N y)).
Proof. exact (MK_COMB (@lem8026737 A M N y) (@lem8026738 A M N y)). Qed.
Lemma lem8026740 {A M N : Type'} (y : type2 A M N) : (term181 A M N y) = (term182 A M N y).
Proof. exact (EQ_MP (@lem8026739 A M N y) (@lem8026731 A M N y)). Qed.
Lemma lem8026741 {A M N : Type'} : (term210 A M N) = (term210 A M N).
Proof. exact (eq_refl (term210 A M N)). Qed.
Lemma lem8026742 {A M N : Type'} (y : type2 A M N) : (term211 A M N y) = (term212 A M N y).
Proof. exact (MK_COMB (@lem8026741 A M N) (@lem8026740 A M N y)). Qed.
Lemma lem8026743 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a0 = (term124 A M N a0 a1).
Proof. exact (@lem51128 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026744 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (@lem8026743 A M N x y). Qed.
Lemma lem8026745 {A M N : Type'} (a0 : cart A M) (a1 : cart A N) : a1 = (term125 A M N a0 a1).
Proof. exact (@lem51159 (cart A M) (cart A N) a0 a1). Qed.
Lemma lem8026746 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (@lem8026745 A M N x y). Qed.
Lemma lem8026747 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8026748 {A M : Type'} : (term126 A M) = (term126 A M).
Proof. exact (eq_refl (term126 A M)). Qed.
Lemma lem8026749 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A M x) = (term128 A M N x y).
Proof. exact (MK_COMB (@lem8026748 A M) (@lem8026744 A M N x y)). Qed.
Lemma lem8026750 {A M N : Type'} (x : cart A M) (y : cart A N) : (term128 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term128 A M N x y)). Qed.
Lemma lem8026751 {A M : Type'} (x : cart A M) : (term129 A M x) = (term129 A M x).
Proof. exact (eq_refl (term129 A M x)). Qed.
Lemma lem8026752 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = ((term127 A M x) = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026751 A M x) (@lem8026750 A M N x y)). Qed.
Lemma lem8026753 {A M : Type'} (x : cart A M) : (term127 A M x) = x.
Proof. exact (eq_refl (term127 A M x)). Qed.
Lemma lem8026754 {A M : Type'} : (@eq (cart A M)) = (@eq (cart A M)).
Proof. exact (eq_refl (@eq (cart A M))). Qed.
Lemma lem8026755 {A M : Type'} (x : cart A M) : (term129 A M x) = (@eq (cart A M) x).
Proof. exact (MK_COMB (@lem8026754 A M) (@lem8026753 A M x)). Qed.
Lemma lem8026756 {A M N : Type'} (x : cart A M) (y : cart A N) : (term124 A M N x y) = (term124 A M N x y).
Proof. exact (eq_refl (term124 A M N x y)). Qed.
Lemma lem8026757 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term124 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026755 A M x) (@lem8026756 A M N x y)). Qed.
Lemma lem8026758 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A M x) = (term128 A M N x y)) = (x = (term124 A M N x y)).
Proof. exact (TRANS (@lem8026752 A M N x y) (@lem8026757 A M N x y)). Qed.
Lemma lem8026759 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026758 A M N x y) (@lem8026749 A M N x y)). Qed.
Lemma lem8026760 {A M : Type'} (x : cart A M) : (@eq (cart A M) x) = (@eq (cart A M) x).
Proof. exact (eq_refl (@eq (cart A M) x)). Qed.
Lemma lem8026761 {A M N : Type'} (x : cart A M) (y : cart A N) : (x = x) = (x = (term124 A M N x y)).
Proof. exact (MK_COMB (@lem8026760 A M x) (@lem8026759 A M N x y)). Qed.
Lemma lem8026762 {A M N : Type'} (x : cart A M) (y : cart A N) : x = (term124 A M N x y).
Proof. exact (EQ_MP (@lem8026761 A M N x y) (@lem8026747 A M x)). Qed.
Lemma lem8026763 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026764 {A N : Type'} : (term126 A N) = (term126 A N).
Proof. exact (eq_refl (term126 A N)). Qed.
Lemma lem8026765 {A M N : Type'} (x : cart A M) (y : cart A N) : (term127 A N y) = (term130 A M N x y).
Proof. exact (MK_COMB (@lem8026764 A N) (@lem8026746 A M N x y)). Qed.
Lemma lem8026766 {A M N : Type'} (x : cart A M) (y : cart A N) : (term130 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term130 A M N x y)). Qed.
Lemma lem8026767 {A N : Type'} (y : cart A N) : (term129 A N y) = (term129 A N y).
Proof. exact (eq_refl (term129 A N y)). Qed.
Lemma lem8026768 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = ((term127 A N y) = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026767 A N y) (@lem8026766 A M N x y)). Qed.
Lemma lem8026769 {A N : Type'} (y : cart A N) : (term127 A N y) = y.
Proof. exact (eq_refl (term127 A N y)). Qed.
Lemma lem8026770 {A N : Type'} : (@eq (cart A N)) = (@eq (cart A N)).
Proof. exact (eq_refl (@eq (cart A N))). Qed.
Lemma lem8026771 {A N : Type'} (y : cart A N) : (term129 A N y) = (@eq (cart A N) y).
Proof. exact (MK_COMB (@lem8026770 A N) (@lem8026769 A N y)). Qed.
Lemma lem8026772 {A M N : Type'} (x : cart A M) (y : cart A N) : (term125 A M N x y) = (term125 A M N x y).
Proof. exact (eq_refl (term125 A M N x y)). Qed.
Lemma lem8026773 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term125 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026771 A N y) (@lem8026772 A M N x y)). Qed.
Lemma lem8026774 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term127 A N y) = (term130 A M N x y)) = (y = (term125 A M N x y)).
Proof. exact (TRANS (@lem8026768 A M N x y) (@lem8026773 A M N x y)). Qed.
Lemma lem8026775 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026774 A M N x y) (@lem8026765 A M N x y)). Qed.
Lemma lem8026776 {A N : Type'} (y : cart A N) : (@eq (cart A N) y) = (@eq (cart A N) y).
Proof. exact (eq_refl (@eq (cart A N) y)). Qed.
Lemma lem8026777 {A M N : Type'} (x : cart A M) (y : cart A N) : (y = y) = (y = (term125 A M N x y)).
Proof. exact (MK_COMB (@lem8026776 A N y) (@lem8026775 A M N x y)). Qed.
Lemma lem8026778 {A M N : Type'} (x : cart A M) (y : cart A N) : y = (term125 A M N x y).
Proof. exact (EQ_MP (@lem8026777 A M N x y) (@lem8026763 A N y)). Qed.
Lemma lem8026779 {A M N : Type'} : (term131 A M N) = (term131 A M N).
Proof. exact (eq_refl (term131 A M N)). Qed.
Lemma lem8026780 {A M N : Type'} (x : cart A M) (y : cart A N) : (term132 A M N x) = (term133 A M N x y).
Proof. exact (MK_COMB (@lem8026779 A M N) (@lem8026762 A M N x y)). Qed.
Lemma lem8026781 {A M N : Type'} (x : cart A M) (y : cart A N) : (term133 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term133 A M N x y)). Qed.
Lemma lem8026782 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term135 A M N x).
Proof. exact (eq_refl (term135 A M N x)). Qed.
Lemma lem8026783 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term132 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026782 A M N x) (@lem8026781 A M N x y)). Qed.
Lemma lem8026784 {A M N : Type'} (x : cart A M) : (term132 A M N x) = (term136 A M N x).
Proof. exact (eq_refl (term132 A M N x)). Qed.
Lemma lem8026785 {A M N : Type'} : (@eq ((cart A N) -> cart A (finite_sum M N))) = (@eq ((cart A N) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq ((cart A N) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026786 {A M N : Type'} (x : cart A M) : (term135 A M N x) = (term137 A M N x).
Proof. exact (MK_COMB (@lem8026785 A M N) (@lem8026784 A M N x)). Qed.
Lemma lem8026787 {A M N : Type'} (x : cart A M) (y : cart A N) : (term134 A M N x y) = (term134 A M N x y).
Proof. exact (eq_refl (term134 A M N x y)). Qed.
Lemma lem8026788 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term134 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (MK_COMB (@lem8026786 A M N x) (@lem8026787 A M N x y)). Qed.
Lemma lem8026789 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term132 A M N x) = (term133 A M N x y)) = ((term136 A M N x) = (term134 A M N x y)).
Proof. exact (TRANS (@lem8026783 A M N x y) (@lem8026788 A M N x y)). Qed.
Lemma lem8026790 {A M N : Type'} (x : cart A M) (y : cart A N) : (term136 A M N x) = (term134 A M N x y).
Proof. exact (EQ_MP (@lem8026789 A M N x y) (@lem8026780 A M N x y)). Qed.
Lemma lem8026791 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (term139 A M N x y).
Proof. exact (MK_COMB (@lem8026790 A M N x y) (@lem8026778 A M N x y)). Qed.
Lemma lem8026792 {A M N : Type'} (x : cart A M) (y : cart A N) : (term139 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term139 A M N x y)). Qed.
Lemma lem8026793 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term141 A M N x y).
Proof. exact (eq_refl (term141 A M N x y)). Qed.
Lemma lem8026794 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((term138 A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026793 A M N x y) (@lem8026792 A M N x y)). Qed.
Lemma lem8026795 {A M N : Type'} (x : cart A M) (y : cart A N) : (term138 A M N x y) = (@pastecart A M N x y).
Proof. exact (eq_refl (term138 A M N x y)). Qed.
Lemma lem8026796 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026797 {A M N : Type'} (x : cart A M) (y : cart A N) : (term141 A M N x y) = (term142 A M N x y).
Proof. exact (MK_COMB (@lem8026796 A M N) (@lem8026795 A M N x y)). Qed.
Lemma lem8026798 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term140 A M N x y)). Qed.
Lemma lem8026799 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term140 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (MK_COMB (@lem8026797 A M N x y) (@lem8026798 A M N x y)). Qed.
Lemma lem8026800 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term138 A M N x y) = (term139 A M N x y)) = ((@pastecart A M N x y) = (term140 A M N x y)).
Proof. exact (TRANS (@lem8026794 A M N x y) (@lem8026799 A M N x y)). Qed.
Lemma lem8026801 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term140 A M N x y).
Proof. exact (EQ_MP (@lem8026800 A M N x y) (@lem8026791 A M N x y)). Qed.
Lemma lem8026802 {A M N : Type'} (x : cart A M) (y : cart A N) : (term140 A M N x y) = (@pastecart A M N x y).
Proof. exact (SYM (@lem8026801 A M N x y)). Qed.
Lemma lem8026803 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (term140 A M N x y).
Proof. exact (eq_refl (term143 A M N x y)). Qed.
Lemma lem8026804 {A M N : Type'} (x : cart A M) (y : cart A N) : (term143 A M N x y) = (@pastecart A M N x y).
Proof. exact (TRANS (@lem8026803 A M N x y) (@lem8026802 A M N x y)). Qed.
Lemma lem8026805 {A M N : Type'} (x : cart A M) : term144 A M N x.
Proof. exact (fun y : cart A N => @lem8026804 A M N x y). Qed.
Lemma lem8026806 {A M N : Type'} : term145 A M N.
Proof. exact (fun x : cart A M => @lem8026805 A M N x). Qed.
Lemma lem8026807 {A M N : Type'} : term146 A M N.
Proof. exact (ex_intro (term147 A M N) (term148 A M N) (@lem8026806 A M N)). Qed.
Lemma lem8026809 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8026810 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (a = b) = (@GEQ (cart A (finite_sum M N)) a b).
Proof. exact (@lem8026809 (type2 A M N) a b). Qed.
Lemma lem8026811 {A M N : Type'} (_105963 : type1162 A M N) (x : cart A M) (y : cart A N) : ((term149 A M N _105963 x y) = (@pastecart A M N x y)) = (term150 A M N _105963 x y).
Proof. exact (@lem8026810 A M N (term149 A M N _105963 x y) (@pastecart A M N x y)). Qed.
Lemma lem8026812 {A M N : Type'} (_105963 : type1162 A M N) (x : cart A M) : (term151 A M N _105963 x) = (term152 A M N _105963 x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026811 A M N _105963 x y)). Qed.
Lemma lem8026813 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026814 {A M N : Type'} (_105963 : type1162 A M N) (x : cart A M) : (term153 A M N _105963 x) = (term154 A M N _105963 x).
Proof. exact (MK_COMB (@lem8026813 A N) (@lem8026812 A M N _105963 x)). Qed.
Lemma lem8026815 {A M N : Type'} (_105963 : type1162 A M N) : (term155 A M N _105963) = (term156 A M N _105963).
Proof. exact (fun_ext (fun x : cart A M => @lem8026814 A M N _105963 x)). Qed.
Lemma lem8026816 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026817 {A M N : Type'} (_105963 : type1162 A M N) : (term157 A M N _105963) = (term158 A M N _105963).
Proof. exact (MK_COMB (@lem8026816 A M) (@lem8026815 A M N _105963)). Qed.
Lemma lem8026818 {A M N : Type'} : (term147 A M N) = (term159 A M N).
Proof. exact (fun_ext (fun _105963 : type1162 A M N => @lem8026817 A M N _105963)). Qed.
Lemma lem8026819 {A M N : Type'} : (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))) = (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex ((prod (cart A M) (cart A N)) -> cart A (finite_sum M N)))). Qed.
Lemma lem8026820 {A M N : Type'} : (term146 A M N) = (term160 A M N).
Proof. exact (MK_COMB (@lem8026819 A M N) (@lem8026818 A M N)). Qed.
Lemma lem8026821 {A M N : Type'} : term160 A M N.
Proof. exact (EQ_MP (@lem8026820 A M N) (@lem8026807 A M N)). Qed.
Lemma lem8026823 {_5076 : Type'} (P : _5076 -> Prop) : term161 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8026824 {A M N : Type'} (P : type280 A M N) : term162 A M N P.
Proof. exact (@lem8026823 (type1162 A M N) P). Qed.
Lemma lem8026825 {A M N : Type'} : term163 A M N.
Proof. exact (@lem8026824 A M N (term159 A M N)). Qed.
Lemma lem8026826 {A M N : Type'} : term164 A M N.
Proof. exact (@lem8026825 A M N (@lem8026821 A M N)). Qed.
Lemma lem8026827 {A M N : Type'} : (term164 A M N) = (term165 A M N).
Proof. exact (eq_refl (term164 A M N)). Qed.
Lemma lem8026828 {A M N : Type'} : term165 A M N.
Proof. exact (EQ_MP (@lem8026827 A M N) (@lem8026826 A M N)). Qed.
Lemma lem8026829 {A M N : Type'} (x : cart A M) : term166 A M N x.
Proof. exact (@lem8026828 A M N x). Qed.
Lemma lem8026830 {A M N : Type'} (x : cart A M) : (term166 A M N x) = (term167 A M N x).
Proof. exact (eq_refl (term166 A M N x)). Qed.
Lemma lem8026831 {A M N : Type'} (x : cart A M) : term167 A M N x.
Proof. exact (EQ_MP (@lem8026830 A M N x) (@lem8026829 A M N x)). Qed.
Lemma lem8026832 {A M N : Type'} (x : cart A M) (y : cart A N) : term168 A M N x y.
Proof. exact (@lem8026831 A M N x y). Qed.
Lemma lem8026833 {A M N : Type'} (x : cart A M) (y : cart A N) : (term168 A M N x y) = (term169 A M N x y).
Proof. exact (eq_refl (term168 A M N x y)). Qed.
Lemma lem8026834 {A M N : Type'} (x : cart A M) (y : cart A N) : term169 A M N x y.
Proof. exact (EQ_MP (@lem8026833 A M N x y) (@lem8026832 A M N x y)). Qed.
Lemma lem8026836 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8026837 {A M N : Type'} (a : type2 A M N) (b : type2 A M N) : (@GEQ (cart A (finite_sum M N)) a b) = (a = b).
Proof. exact (@lem8026836 (type2 A M N) a b). Qed.
Lemma lem8026838 {A M N : Type'} (x : cart A M) (y : cart A N) : (term169 A M N x y) = ((term170 A M N x y) = (@pastecart A M N x y)).
Proof. exact (@lem8026837 A M N (term170 A M N x y) (@pastecart A M N x y)). Qed.
Lemma lem8026839 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (EQ_MP (@lem8026838 A M N x y) (@lem8026834 A M N x y)). Qed.
Lemma lem8026840 {A M N : Type'} (x : cart A M) (y : cart A N) : (term170 A M N x y) = (@pastecart A M N x y).
Proof. exact (@lem8026839 A M N x y). Qed.
Lemma lem8026841 {A M N : Type'} (y : type2 A M N) : (term212 A M N y) = (term213 A M N y).
Proof. exact (@lem8026840 A M N (@fstcart A M N y) (@sndcart A M N y)). Qed.
Lemma lem8026842 {A M N : Type'} (y : type2 A M N) : (term211 A M N y) = (term213 A M N y).
Proof. exact (TRANS (@lem8026742 A M N y) (@lem8026841 A M N y)). Qed.
Lemma lem8026843 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026844 {A M N : Type'} (y : type2 A M N) : (term214 A M N y) = (term215 A M N y).
Proof. exact (MK_COMB (@lem8026843 A M N) (@lem8026842 A M N y)). Qed.
Lemma lem8026845 {A M N : Type'} (y : type2 A M N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026846 {A M N : Type'} (y : type2 A M N) : ((term211 A M N y) = y) = ((term213 A M N y) = y).
Proof. exact (MK_COMB (@lem8026844 A M N y) (@lem8026845 A M N y)). Qed.
Lemma lem8026849 {A M N : Type'} (s : type24 A M) (t : type24 A N) (y : type2 A M N) : (term216 A M N s t y) = (term217 A M N s t y).
Proof. exact (MK_COMB (@lem8026717 A M N y s t) (@lem8026846 A M N y)). Qed.
Lemma lem8026852 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term218 A M N y s t) = (term218 A M N y s t).
Proof. exact (eq_refl (term218 A M N y s t)). Qed.
Lemma lem8026853 {A M N : Type'} (s : type24 A M) (t : type24 A N) (y : type2 A M N) : (term219 A M N s t y) = (term220 A M N s t y).
Proof. exact (MK_COMB (@lem8026852 A M N y s t) (@lem8026849 A M N s t y)). Qed.
Lemma lem8026856 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term221 A M N s t) = (term222 A M N s t).
Proof. exact (fun_ext (fun y : type2 A M N => @lem8026853 A M N s t y)). Qed.
Lemma lem8026857 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem8026858 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term223 A M N s t) = (term224 A M N s t).
Proof. exact (MK_COMB (@lem8026857 A M N) (@lem8026856 A M N s t)). Qed.
Lemma lem8026863 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term225 A M N s t) = (term226 A M N s t).
Proof. exact (MK_COMB (@lem8026680 A M N s t) (@lem8026858 A M N s t)). Qed.
Lemma lem8026866 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term226 A M N s t) = (term225 A M N s t).
Proof. exact (SYM (@lem8026863 A M N s t)). Qed.
Lemma lem8026896 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term15 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem8026146 _88435 _88436 P a b) (@lem8026145 _88435 _88436 P a b)). Qed.
Lemma lem8026897 {A M N : Type'} (P : type22 A M N) (a : cart A M) (b : cart A N) : (term227 A M N a b P) = (P a b).
Proof. exact (@lem8026896 (cart A N) (cart A M) P a b). Qed.
Lemma lem8026898 {A M N : Type'} (s : type24 A M) (t : type24 A N) (y : type2 A M N) : (term228 A M N y s t) = (term229 A M N s t y).
Proof. exact (@lem8026897 A M N (term77 A M N s t) (@fstcart A M N y) (@sndcart A M N y)). Qed.
Lemma lem8026899 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term79 A M N s t x) = (term80 A M N x s t).
Proof. exact (eq_refl (term79 A M N s t x)). Qed.
Lemma lem8026900 {A N : Type'} (y : cart A N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026901 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (y : cart A N) : (term81 A M N s t x y) = (term82 A M N x s t y).
Proof. exact (MK_COMB (@lem8026899 A M N x s t) (@lem8026900 A N y)). Qed.
Lemma lem8026902 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term82 A M N x s t y) = (term24 A M N x s y t).
Proof. exact (eq_refl (term82 A M N x s t y)). Qed.
Lemma lem8026903 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term81 A M N s t x y) = (term24 A M N x s y t).
Proof. exact (TRANS (@lem8026901 A M N x s t y) (@lem8026902 A M N x s y t)). Qed.
Lemma lem8026904 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) : (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129) = (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129).
Proof. exact (eq_refl (@SETSPEC (prod (cart A M) (cart A N)) GEN_PVAR_129)). Qed.
Lemma lem8026905 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term83 A M N GEN_PVAR_129 s t x y) = (term84 A M N GEN_PVAR_129 x s y t).
Proof. exact (MK_COMB (@lem8026904 A M N GEN_PVAR_129) (@lem8026903 A M N x s y t)). Qed.
Lemma lem8026906 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y).
Proof. exact (eq_refl (@pair (cart A M) (cart A N) x y)). Qed.
Lemma lem8026907 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term85 A M N GEN_PVAR_129 s t x y) = (term86 A M N GEN_PVAR_129 s t x y).
Proof. exact (MK_COMB (@lem8026905 A M N GEN_PVAR_129 x s y t) (@lem8026906 A M N x y)). Qed.
Lemma lem8026908 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) : (term87 A M N GEN_PVAR_129 s t x) = (term88 A M N GEN_PVAR_129 s t x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026907 A M N GEN_PVAR_129 s t x y)). Qed.
Lemma lem8026909 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8026910 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) (x : cart A M) : (term89 A M N GEN_PVAR_129 s t x) = (term90 A M N GEN_PVAR_129 s t x).
Proof. exact (MK_COMB (@lem8026909 A N) (@lem8026908 A M N GEN_PVAR_129 s t x)). Qed.
Lemma lem8026911 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term91 A M N GEN_PVAR_129 s t) = (term92 A M N GEN_PVAR_129 s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8026910 A M N GEN_PVAR_129 s t x)). Qed.
Lemma lem8026912 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8026913 {A M N : Type'} (GEN_PVAR_129 : type1642 A M N) (s : type24 A M) (t : type24 A N) : (term93 A M N GEN_PVAR_129 s t) = (term94 A M N GEN_PVAR_129 s t).
Proof. exact (MK_COMB (@lem8026912 A M) (@lem8026911 A M N GEN_PVAR_129 s t)). Qed.
Lemma lem8026914 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term95 A M N s t) = (term96 A M N s t).
Proof. exact (fun_ext (fun GEN_PVAR_129 : type1642 A M N => @lem8026913 A M N GEN_PVAR_129 s t)). Qed.
Lemma lem8026915 {A M N : Type'} : (@GSPEC (prod (cart A M) (cart A N))) = (@GSPEC (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@GSPEC (prod (cart A M) (cart A N)))). Qed.
Lemma lem8026916 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term97 A M N s t) = (term72 A M N s t).
Proof. exact (MK_COMB (@lem8026915 A M N) (@lem8026914 A M N s t)). Qed.
Lemma lem8026917 {A M N : Type'} (y : type2 A M N) : (term205 A M N y) = (term205 A M N y).
Proof. exact (eq_refl (term205 A M N y)). Qed.
Lemma lem8026918 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term228 A M N y s t) = (term207 A M N y s t).
Proof. exact (MK_COMB (@lem8026917 A M N y) (@lem8026916 A M N s t)). Qed.
Lemma lem8026919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8026920 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term230 A M N y s t) = (term231 A M N y s t).
Proof. exact (MK_COMB (@lem8026919) (@lem8026918 A M N y s t)). Qed.
Lemma lem8026921 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term232 A M N s t y) = (term233 A M N y s t).
Proof. exact (eq_refl (term232 A M N s t y)). Qed.
Lemma lem8026922 {A M N : Type'} (y : type2 A M N) : (@sndcart A M N y) = (@sndcart A M N y).
Proof. exact (eq_refl (@sndcart A M N y)). Qed.
Lemma lem8026923 {A M N : Type'} (s : type24 A M) (t : type24 A N) (y : type2 A M N) : (term229 A M N s t y) = (term234 A M N s t y).
Proof. exact (MK_COMB (@lem8026921 A M N y s t) (@lem8026922 A M N y)). Qed.
Lemma lem8026924 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term234 A M N s t y) = (term235 A M N s y t).
Proof. exact (eq_refl (term234 A M N s t y)). Qed.
Lemma lem8026925 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term229 A M N s t y) = (term235 A M N s y t).
Proof. exact (TRANS (@lem8026923 A M N s t y) (@lem8026924 A M N s y t)). Qed.
Lemma lem8026926 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : ((term228 A M N y s t) = (term229 A M N s t y)) = ((term207 A M N y s t) = (term235 A M N s y t)).
Proof. exact (MK_COMB (@lem8026920 A M N y s t) (@lem8026925 A M N s y t)). Qed.
Lemma lem8026927 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term207 A M N y s t) = (term235 A M N s y t).
Proof. exact (EQ_MP (@lem8026926 A M N s y t) (@lem8026898 A M N s t y)). Qed.
Lemma lem8026930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8026931 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term209 A M N y s t) = (term236 A M N s y t).
Proof. exact (MK_COMB (@lem8026930) (@lem8026927 A M N s y t)). Qed.
Lemma lem8026935 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term9 _140390 _140392 _140395 z) = z.
Proof. exact (EQ_MP (@lem8026137 _140390 _140392 _140395 z) (@lem8026136 _140390 _140392 _140395 z)). Qed.
Lemma lem8026936 {A M N : Type'} (z : type2 A M N) : (term213 A M N z) = z.
Proof. exact (@lem8026935 N M A z). Qed.
Lemma lem8026937 {A M N : Type'} (y : type2 A M N) : (term213 A M N y) = y.
Proof. exact (@lem8026936 A M N y). Qed.
Lemma lem8026938 {A M N : Type'} : (@eq (cart A (finite_sum M N))) = (@eq (cart A (finite_sum M N))).
Proof. exact (eq_refl (@eq (cart A (finite_sum M N)))). Qed.
Lemma lem8026939 {A M N : Type'} (y : type2 A M N) : (term215 A M N y) = (@eq (cart A (finite_sum M N)) y).
Proof. exact (MK_COMB (@lem8026938 A M N) (@lem8026937 A M N y)). Qed.
Lemma lem8026940 {A M N : Type'} (y : type2 A M N) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8026941 {A M N : Type'} (y : type2 A M N) : ((term213 A M N y) = y) = (y = y).
Proof. exact (MK_COMB (@lem8026939 A M N y) (@lem8026940 A M N y)). Qed.
Lemma lem8026943 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8026944 {A M N : Type'} (x : type2 A M N) : (x = x) = True.
Proof. exact (@lem8026943 (type2 A M N) x). Qed.
Lemma lem8026945 {A M N : Type'} (y : type2 A M N) : (y = y) = True.
Proof. exact (@lem8026944 A M N y). Qed.
Lemma lem8026946 {A M N : Type'} (y : type2 A M N) : ((term213 A M N y) = y) = True.
Proof. exact (TRANS (@lem8026941 A M N y) (@lem8026945 A M N y)). Qed.
Lemma lem8026947 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term217 A M N s t y) = (term237 A M N s y t).
Proof. exact (MK_COMB (@lem8026931 A M N s y t) (@lem8026946 A M N y)). Qed.
Lemma lem8026949 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8026950 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term237 A M N s y t) = (term235 A M N s y t).
Proof. exact (@lem8026949 (term235 A M N s y t)). Qed.
Lemma lem8026953 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term217 A M N s t y) = (term235 A M N s y t).
Proof. exact (TRANS (@lem8026947 A M N s y t) (@lem8026950 A M N s y t)). Qed.
Lemma lem8026954 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term218 A M N y s t) = (term218 A M N y s t).
Proof. exact (eq_refl (term218 A M N y s t)). Qed.
Lemma lem8026955 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term220 A M N s t y) = (term238 A M N s y t).
Proof. exact (MK_COMB (@lem8026954 A M N y s t) (@lem8026953 A M N s y t)). Qed.
Lemma lem8026958 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term222 A M N s t) = (term239 A M N s t).
Proof. exact (fun_ext (fun y : type2 A M N => @lem8026955 A M N s y t)). Qed.
Lemma lem8026959 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem8026960 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term224 A M N s t) = (term240 A M N s t).
Proof. exact (MK_COMB (@lem8026959 A M N) (@lem8026958 A M N s t)). Qed.
Lemma lem8026965 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term200 A M N s t) = (term200 A M N s t).
Proof. exact (eq_refl (term200 A M N s t)). Qed.
Lemma lem8026966 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term226 A M N s t) = (term241 A M N s t).
Proof. exact (MK_COMB (@lem8026965 A M N s t) (@lem8026960 A M N s t)). Qed.
Lemma lem8026969 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term241 A M N s t) = (term226 A M N s t).
Proof. exact (SYM (@lem8026966 A M N s t)). Qed.
Lemma lem8026991 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem8026134 A M N y x) (@lem8026133 A M N x y)). Qed.
Lemma lem8026992 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (@lem8026991 A M N y x). Qed.
Lemma lem8026993 {A M N : Type'} : (@pair (cart A M) (cart A N)) = (@pair (cart A M) (cart A N)).
Proof. exact (eq_refl (@pair (cart A M) (cart A N))). Qed.
Lemma lem8026994 {A M N : Type'} (y : cart A N) (x : cart A M) : (term189 A M N x y) = (@pair (cart A M) (cart A N) x).
Proof. exact (MK_COMB (@lem8026993 A M N) (@lem8026992 A M N y x)). Qed.
Lemma lem8026996 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8026128 A M N x y) (@lem8026127 A M N x y)). Qed.
Lemma lem8026997 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (@lem8026996 A M N x y). Qed.
Lemma lem8026998 {A M N : Type'} (x : cart A M) (y : cart A N) : (term191 A M N x y) = (@pair (cart A M) (cart A N) x y).
Proof. exact (MK_COMB (@lem8026994 A M N y x) (@lem8026997 A M N x y)). Qed.
Lemma lem8026999 {A M N : Type'} : (@eq (prod (cart A M) (cart A N))) = (@eq (prod (cart A M) (cart A N))).
Proof. exact (eq_refl (@eq (prod (cart A M) (cart A N)))). Qed.
Lemma lem8027000 {A M N : Type'} (x : cart A M) (y : cart A N) : (term192 A M N x y) = (term242 A M N x y).
Proof. exact (MK_COMB (@lem8026999 A M N) (@lem8026998 A M N x y)). Qed.
Lemma lem8027001 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y).
Proof. exact (eq_refl (@pair (cart A M) (cart A N) x y)). Qed.
Lemma lem8027002 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term191 A M N x y) = (@pair (cart A M) (cart A N) x y)) = ((@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y)).
Proof. exact (MK_COMB (@lem8027000 A M N x y) (@lem8027001 A M N x y)). Qed.
Lemma lem8027004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8027005 {A M N : Type'} (x : type1642 A M N) : (x = x) = True.
Proof. exact (@lem8027004 (type1642 A M N) x). Qed.
Lemma lem8027006 {A M N : Type'} (x : cart A M) (y : cart A N) : ((@pair (cart A M) (cart A N) x y) = (@pair (cart A M) (cart A N) x y)) = True.
Proof. exact (@lem8027005 A M N (@pair (cart A M) (cart A N) x y)). Qed.
Lemma lem8027007 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term191 A M N x y) = (@pair (cart A M) (cart A N) x y)) = True.
Proof. exact (TRANS (@lem8027002 A M N x y) (@lem8027006 A M N x y)). Qed.
Lemma lem8027008 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term175 A M N x s y t) = (term175 A M N x s y t).
Proof. exact (eq_refl (term175 A M N x s y t)). Qed.
Lemma lem8027009 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term193 A M N s t x y) = (term243 A M N x s y t).
Proof. exact (MK_COMB (@lem8027008 A M N x s y t) (@lem8027007 A M N x y)). Qed.
Lemma lem8027011 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8027012 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term243 A M N x s y t) = (term24 A M N x s y t).
Proof. exact (@lem8027011 (term24 A M N x s y t)). Qed.
Lemma lem8027015 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term193 A M N s t x y) = (term24 A M N x s y t).
Proof. exact (TRANS (@lem8027009 A M N x s y t) (@lem8027012 A M N x s y t)). Qed.
Lemma lem8027016 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term112 A M N x s y t) = (term112 A M N x s y t).
Proof. exact (eq_refl (term112 A M N x s y t)). Qed.
Lemma lem8027017 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term194 A M N s t x y) = (term244 A M N x s y t).
Proof. exact (MK_COMB (@lem8027016 A M N x s y t) (@lem8027015 A M N x s y t)). Qed.
Lemma lem8027019 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem8027020 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term244 A M N x s y t) = True.
Proof. exact (@lem8027019 (term24 A M N x s y t)). Qed.
Lemma lem8027021 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) (y : cart A N) : (term194 A M N s t x y) = True.
Proof. exact (TRANS (@lem8027017 A M N x s y t) (@lem8027020 A M N x s y t)). Qed.
Lemma lem8027022 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term195 A M N s t x) = (term245 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem8027021 A M N s t x y)). Qed.
Lemma lem8027023 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8027024 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term196 A M N s t x) = (term246 A N).
Proof. exact (MK_COMB (@lem8027023 A N) (@lem8027022 A M N s t x)). Qed.
Lemma lem8027026 {A : Type'} (t : Prop) : (term247 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8027027 {A N : Type'} (t : Prop) : (term248 A N t) = t.
Proof. exact (@lem8027026 (cart A N) t). Qed.
Lemma lem8027028 {A N : Type'} : (term246 A N) = True.
Proof. exact (@lem8027027 A N True). Qed.
Lemma lem8027029 {A M N : Type'} (s : type24 A M) (t : type24 A N) (x : cart A M) : (term196 A M N s t x) = True.
Proof. exact (TRANS (@lem8027024 A M N s t x) (@lem8027028 A N)). Qed.
Lemma lem8027030 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term197 A M N s t) = (term245 A M).
Proof. exact (fun_ext (fun x : cart A M => @lem8027029 A M N s t x)). Qed.
Lemma lem8027031 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8027032 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term198 A M N s t) = (term246 A M).
Proof. exact (MK_COMB (@lem8027031 A M) (@lem8027030 A M N s t)). Qed.
Lemma lem8027034 {A : Type'} (t : Prop) : (term247 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8027035 {A M : Type'} (t : Prop) : (term248 A M t) = t.
Proof. exact (@lem8027034 (cart A M) t). Qed.
Lemma lem8027036 {A M : Type'} : (term246 A M) = True.
Proof. exact (@lem8027035 A M True). Qed.
Lemma lem8027037 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term198 A M N s t) = True.
Proof. exact (TRANS (@lem8027032 A M N s t) (@lem8027036 A M)). Qed.
Lemma lem8027038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8027039 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term200 A M N s t) = (and True).
Proof. exact (MK_COMB (@lem8027038) (@lem8027037 A M N s t)). Qed.
Lemma lem8027041 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term249 _141853 _141854 _141855 s t P) = (term250 _141853 _141854 _141855 s t P).
Proof. exact (EQ_MP (@lem8003920 _141853 _141854 _141855 s t P) (@lem0)). Qed.
Lemma lem8027042 {A M N : Type'} (s : type24 A M) (t : type24 A N) (P : type16 A M N) : (term249 A M N s t P) = (term250 A M N s t P).
Proof. exact (@lem8027041 A M N s t P). Qed.
Lemma lem8027043 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term251 A M N s t) = (term252 A M N s t).
Proof. exact (@lem8027042 A M N s t (term253 A M N s t)). Qed.
Lemma lem8027044 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term254 A M N s t y) = (term235 A M N s y t).
Proof. exact (eq_refl (term254 A M N s t y)). Qed.
Lemma lem8027045 {A M N : Type'} (y : type2 A M N) (s : type24 A M) (t : type24 A N) : (term218 A M N y s t) = (term218 A M N y s t).
Proof. exact (eq_refl (term218 A M N y s t)). Qed.
Lemma lem8027046 {A M N : Type'} (s : type24 A M) (y : type2 A M N) (t : type24 A N) : (term255 A M N s t y) = (term238 A M N s y t).
Proof. exact (MK_COMB (@lem8027045 A M N y s t) (@lem8027044 A M N s y t)). Qed.
Lemma lem8027047 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term256 A M N s t) = (term239 A M N s t).
Proof. exact (fun_ext (fun y : type2 A M N => @lem8027046 A M N s y t)). Qed.
Lemma lem8027048 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem8027049 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term251 A M N s t) = (term240 A M N s t).
Proof. exact (MK_COMB (@lem8027048 A M N) (@lem8027047 A M N s t)). Qed.
Lemma lem8027050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8027051 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term257 A M N s t) = (term258 A M N s t).
Proof. exact (MK_COMB (@lem8027050) (@lem8027049 A M N s t)). Qed.
Lemma lem8027052 {A M N : Type'} (s : type24 A M) (x : cart A M) (y : cart A N) (t : type24 A N) : (term259 A M N s t x y) = (term260 A M N s x y t).
Proof. exact (eq_refl (term259 A M N s t x y)). Qed.
Lemma lem8027053 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term112 A M N x s y t) = (term112 A M N x s y t).
Proof. exact (eq_refl (term112 A M N x s y t)). Qed.
Lemma lem8027054 {A M N : Type'} (s : type24 A M) (x : cart A M) (y : cart A N) (t : type24 A N) : (term261 A M N s t x y) = (term262 A M N s x y t).
Proof. exact (MK_COMB (@lem8027053 A M N x s y t) (@lem8027052 A M N s x y t)). Qed.
Lemma lem8027055 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) : (term263 A M N s t x) = (term264 A M N s x t).
Proof. exact (fun_ext (fun y : cart A N => @lem8027054 A M N s x y t)). Qed.
Lemma lem8027056 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8027057 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) : (term265 A M N s t x) = (term266 A M N s x t).
Proof. exact (MK_COMB (@lem8027056 A N) (@lem8027055 A M N s x t)). Qed.
Lemma lem8027058 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term267 A M N s t) = (term268 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8027057 A M N s x t)). Qed.
Lemma lem8027059 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8027060 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term252 A M N s t) = (term269 A M N s t).
Proof. exact (MK_COMB (@lem8027059 A M) (@lem8027058 A M N s t)). Qed.
Lemma lem8027061 {A M N : Type'} (s : type24 A M) (t : type24 A N) : ((term251 A M N s t) = (term252 A M N s t)) = ((term240 A M N s t) = (term269 A M N s t)).
Proof. exact (MK_COMB (@lem8027051 A M N s t) (@lem8027060 A M N s t)). Qed.
Lemma lem8027062 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term240 A M N s t) = (term269 A M N s t).
Proof. exact (EQ_MP (@lem8027061 A M N s t) (@lem8027043 A M N s t)). Qed.
Lemma lem8027078 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem8026134 A M N y x) (@lem8026133 A M N x y)). Qed.
Lemma lem8027079 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (@lem8027078 A M N y x). Qed.
Lemma lem8027080 {A M : Type'} : (@IN (cart A M)) = (@IN (cart A M)).
Proof. exact (eq_refl (@IN (cart A M))). Qed.
Lemma lem8027081 {A M N : Type'} (y : cart A N) (x : cart A M) : (term270 A M N x y) = (@IN (cart A M) x).
Proof. exact (MK_COMB (@lem8027080 A M) (@lem8027079 A M N y x)). Qed.
Lemma lem8027082 {A M : Type'} (s : type24 A M) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8027083 {A M N : Type'} (y : cart A N) (x : cart A M) (s : type24 A M) : (term271 A M N x y s) = (@IN (cart A M) x s).
Proof. exact (MK_COMB (@lem8027081 A M N y x) (@lem8027082 A M s)). Qed.
Lemma lem8027084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8027085 {A M N : Type'} (y : cart A N) (x : cart A M) (s : type24 A M) : (term272 A M N x y s) = (term273 A M x s).
Proof. exact (MK_COMB (@lem8027084) (@lem8027083 A M N y x s)). Qed.
Lemma lem8027087 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8026128 A M N x y) (@lem8026127 A M N x y)). Qed.
Lemma lem8027088 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (@lem8027087 A M N x y). Qed.
Lemma lem8027089 {A N : Type'} : (@IN (cart A N)) = (@IN (cart A N)).
Proof. exact (eq_refl (@IN (cart A N))). Qed.
Lemma lem8027090 {A M N : Type'} (x : cart A M) (y : cart A N) : (term274 A M N x y) = (@IN (cart A N) y).
Proof. exact (MK_COMB (@lem8027089 A N) (@lem8027088 A M N x y)). Qed.
Lemma lem8027091 {A N : Type'} (t : type24 A N) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem8027092 {A M N : Type'} (x : cart A M) (y : cart A N) (t : type24 A N) : (term275 A M N x y t) = (@IN (cart A N) y t).
Proof. exact (MK_COMB (@lem8027090 A M N x y) (@lem8027091 A N t)). Qed.
Lemma lem8027093 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term260 A M N s x y t) = (term24 A M N x s y t).
Proof. exact (MK_COMB (@lem8027085 A M N y x s) (@lem8027092 A M N x y t)). Qed.
Lemma lem8027096 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term112 A M N x s y t) = (term112 A M N x s y t).
Proof. exact (eq_refl (term112 A M N x s y t)). Qed.
Lemma lem8027097 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term262 A M N s x y t) = (term244 A M N x s y t).
Proof. exact (MK_COMB (@lem8027096 A M N x s y t) (@lem8027093 A M N x s y t)). Qed.
Lemma lem8027099 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem8027100 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term244 A M N x s y t) = True.
Proof. exact (@lem8027099 (term24 A M N x s y t)). Qed.
Lemma lem8027101 {A M N : Type'} (s : type24 A M) (x : cart A M) (y : cart A N) (t : type24 A N) : (term262 A M N s x y t) = True.
Proof. exact (TRANS (@lem8027097 A M N x s y t) (@lem8027100 A M N x s y t)). Qed.
Lemma lem8027102 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) : (term264 A M N s x t) = (term245 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem8027101 A M N s x y t)). Qed.
Lemma lem8027103 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8027104 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) : (term266 A M N s x t) = (term246 A N).
Proof. exact (MK_COMB (@lem8027103 A N) (@lem8027102 A M N s x t)). Qed.
Lemma lem8027106 {A : Type'} (t : Prop) : (term247 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8027107 {A N : Type'} (t : Prop) : (term248 A N t) = t.
Proof. exact (@lem8027106 (cart A N) t). Qed.
Lemma lem8027108 {A N : Type'} : (term246 A N) = True.
Proof. exact (@lem8027107 A N True). Qed.
Lemma lem8027109 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) : (term266 A M N s x t) = True.
Proof. exact (TRANS (@lem8027104 A M N s x t) (@lem8027108 A N)). Qed.
Lemma lem8027110 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term268 A M N s t) = (term245 A M).
Proof. exact (fun_ext (fun x : cart A M => @lem8027109 A M N s x t)). Qed.
Lemma lem8027111 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8027112 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term269 A M N s t) = (term246 A M).
Proof. exact (MK_COMB (@lem8027111 A M) (@lem8027110 A M N s t)). Qed.
Lemma lem8027114 {A : Type'} (t : Prop) : (term247 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8027115 {A M : Type'} (t : Prop) : (term248 A M t) = t.
Proof. exact (@lem8027114 (cart A M) t). Qed.
Lemma lem8027116 {A M : Type'} : (term246 A M) = True.
Proof. exact (@lem8027115 A M True). Qed.
Lemma lem8027117 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term269 A M N s t) = True.
Proof. exact (TRANS (@lem8027112 A M N s t) (@lem8027116 A M)). Qed.
Lemma lem8027118 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term240 A M N s t) = True.
Proof. exact (TRANS (@lem8027062 A M N s t) (@lem8027117 A M N s t)). Qed.
Lemma lem8027119 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term241 A M N s t) = (True /\ True).
Proof. exact (MK_COMB (@lem8027039 A M N s t) (@lem8027118 A M N s t)). Qed.
Lemma lem8027121 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8027122 : (True /\ True) = True.
Proof. exact (@lem8027121 True). Qed.
Lemma lem8027123 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term241 A M N s t) = True.
Proof. exact (TRANS (@lem8027119 A M N s t) (@lem8027122)). Qed.
Lemma lem8027124 {A M N : Type'} (s : type24 A M) (t : type24 A N) : True = (term241 A M N s t).
Proof. exact (SYM (@lem8027123 A M N s t)). Qed.
Lemma lem8027125 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term241 A M N s t.
Proof. exact (EQ_MP (@lem8027124 A M N s t) (@lem0)). Qed.
Lemma lem8027126 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term226 A M N s t.
Proof. exact (EQ_MP (@lem8026969 A M N s t) (@lem8027125 A M N s t)). Qed.
Lemma lem8027127 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term225 A M N s t.
Proof. exact (EQ_MP (@lem8026866 A M N s t) (@lem8027126 A M N s t)). Qed.
Lemma lem8027128 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term276 A M N s t.
Proof. exact (ex_intro (term277 A M N s t) (term180 A M N) (@lem8027127 A M N s t)). Qed.
Lemma lem8027129 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term278 A M N s t.
Proof. exact (ex_intro (term279 A M N s t) (term210 A M N) (@lem8027128 A M N s t)). Qed.
Lemma lem8027130 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term280 A M N s t.
Proof. exact (@lem8026255 A M N s t (@lem8027129 A M N s t)). Qed.
Lemma lem8027131 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : term281 A M N s t m n.
Proof. exact (@lem8027130 A M N s t (Nat.mul m n)). Qed.
Lemma lem8027132 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term281 A M N s t m n) = ((term67 A M N s t m n) = (term69 A M N s t m n)).
Proof. exact (eq_refl (term281 A M N s t m n)). Qed.
Lemma lem8027133 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : (term67 A M N s t m n) = (term69 A M N s t m n).
Proof. exact (EQ_MP (@lem8027132 A M N s t m n) (@lem8027131 A M N s t m n)). Qed.
Lemma lem8027134 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : term282 A M N s t m n.
Proof. exact (@lem8026251 A M N s t m n (@lem8027133 A M N s t m n)). Qed.
Lemma lem8027135 {A M N : Type'} (s : type24 A M) (m : nat) (t : type24 A N) (n : nat) (h1 : term65 A M N s m t n) : term69 A M N s t m n.
Proof. exact (@lem8027134 A M N s t m n (@lem8026248 A M N s m t n h1)). Qed.
Lemma lem8027136 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) (n : nat) : term283 A M N s t m n.
Proof. exact (fun h0 : term65 A M N s m t n => @lem8027135 A M N s m t n h0). Qed.
Lemma lem8027141 {A M N : Type'} (s : type24 A M) (t : type24 A N) (m : nat) : term284 A M N s t m.
Proof. exact (fun n : nat => @lem8027136 A M N s t m n). Qed.
Lemma lem8027146 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term285 A M N s t.
Proof. exact (fun m : nat => @lem8027141 A M N s t m). Qed.
Lemma lem8027151 {A M N : Type'} (s : type24 A M) : term286 A M N s.
Proof. exact (fun t : type24 A N => @lem8027146 A M N s t). Qed.
Lemma lem8027156 {A M N : Type'} : term287 A M N.
Proof. exact (fun s : type24 A M => @lem8027151 A M N s). Qed.
