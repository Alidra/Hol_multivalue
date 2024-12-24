Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1046224_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import MULT_SYM_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1032609_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1033071 (m : nat) : term0 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem1033072 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1033073 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1033072 m) (@lem1033071 m)). Qed.
Lemma lem1033074 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1033073 m n). Qed.
Lemma lem1033075 (m : nat) (n : nat) : (term2 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1033077 (m : nat) : term4 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1033078 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1033079 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1033078 m) (@lem1033077 m)). Qed.
Lemma lem1033080 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1033079 m n). Qed.
Lemma lem1033081 (m : nat) (n : nat) : (term6 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1033083 (m : nat) : term7 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1033084 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1033085 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1033084 m) (@lem1033083 m)). Qed.
Lemma lem1033086 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1033085 m n). Qed.
Lemma lem1033087 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1033088 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1033087 m n) (@lem1033086 m n)). Qed.
Lemma lem1033089 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1033088 m n p). Qed.
Lemma lem1033090 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1033092 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1033093 {A : Type'} (x : A) : (term12 A x) = ((x = x) = True).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem1033095 (n : nat) (m : nat) (p : nat) : term13 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1033135 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem1033095 n m p)). Qed.
Lemma lem1033136 (b : nat) (e : nat) (d : nat) : (term14 e b d) = (term14 b e d).
Proof. exact (@lem1033135 b e d). Qed.
Lemma lem1033144 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1033145 (d : nat) (e : nat) : (Nat.add e d) = (Nat.add d e).
Proof. exact (@lem1033144 d e). Qed.
Lemma lem1033149 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem1033150 (b : nat) (d : nat) (e : nat) : (term14 b e d) = (term14 b d e).
Proof. exact (MK_COMB (@lem1033149 b) (@lem1033145 d e)). Qed.
Lemma lem1033157 (b : nat) (d : nat) (e : nat) : (term14 e b d) = (term14 b d e).
Proof. exact (TRANS (@lem1033136 b e d) (@lem1033150 b d e)). Qed.
Lemma lem1033158 (c : nat) : (Nat.add c) = (Nat.add c).
Proof. exact (eq_refl (Nat.add c)). Qed.
Lemma lem1033159 (c : nat) (b : nat) (d : nat) (e : nat) : (term15 c e b d) = (term15 c b d e).
Proof. exact (MK_COMB (@lem1033158 c) (@lem1033157 b d e)). Qed.
Lemma lem1033161 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem1033095 n m p)). Qed.
Lemma lem1033162 (b : nat) (c : nat) (d : nat) (e : nat) : (term15 c b d e) = (term15 b c d e).
Proof. exact (@lem1033161 b c (Nat.add d e)). Qed.
Lemma lem1033178 (b : nat) (c : nat) (d : nat) (e : nat) : (term15 c e b d) = (term15 b c d e).
Proof. exact (TRANS (@lem1033159 c b d e) (@lem1033162 b c d e)). Qed.
Lemma lem1033179 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1033180 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term16 a c e b d) = (term16 a b c d e).
Proof. exact (MK_COMB (@lem1033179 a) (@lem1033178 b c d e)). Qed.
Lemma lem1033187 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term17 a b c d e) = (term17 a b c d e).
Proof. exact (eq_refl (term17 a b c d e)). Qed.
Lemma lem1033188 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term16 a b c d e) = (term16 a c e b d)) = ((term16 a b c d e) = (term16 a b c d e)).
Proof. exact (MK_COMB (@lem1033187 a b c d e) (@lem1033180 a b c d e)). Qed.
Lemma lem1033190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1033093 A x) (@lem1033092 A x)). Qed.
Lemma lem1033191 (x : nat) : (x = x) = True.
Proof. exact (@lem1033190 nat x). Qed.
Lemma lem1033192 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term16 a b c d e) = (term16 a b c d e)) = True.
Proof. exact (@lem1033191 (term16 a b c d e)). Qed.
Lemma lem1033193 (a : nat) (c : nat) (e : nat) (b : nat) (d : nat) : ((term16 a b c d e) = (term16 a c e b d)) = True.
Proof. exact (TRANS (@lem1033188 a b c d e) (@lem1033192 a b c d e)). Qed.
Lemma lem1033194 (a : nat) (c : nat) (e : nat) (b : nat) (d : nat) : True = ((term16 a b c d e) = (term16 a c e b d)).
Proof. exact (SYM (@lem1033193 a c e b d)). Qed.
Lemma lem1033199 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term18 m n p)) : (term14 m n p) = (term18 m n p).
Proof. exact (h1). Qed.
Lemma lem1033200 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term18 m n p)) : (term18 m n p) = (term14 m n p).
Proof. exact (SYM (@lem1033199 m n p h1)). Qed.
Lemma lem1033201 (m : nat) (n : nat) (p : nat) (h1 : (term18 m n p) = (term14 m n p)) : (term18 m n p) = (term14 m n p).
Proof. exact (h1). Qed.
Lemma lem1033202 (m : nat) (n : nat) (p : nat) (h1 : (term18 m n p) = (term14 m n p)) : (term14 m n p) = (term18 m n p).
Proof. exact (SYM (@lem1033201 m n p h1)). Qed.
Lemma lem1033203 (m : nat) (n : nat) (p : nat) : ((term14 m n p) = (term18 m n p)) = ((term18 m n p) = (term14 m n p)).
Proof. exact (prop_ext (fun h1 : (term14 m n p) = (term18 m n p) => @lem1033200 m n p h1) (fun h1 : (term18 m n p) = (term14 m n p) => @lem1033202 m n p h1)). Qed.
Lemma lem1033204 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (fun_ext (fun p : nat => @lem1033203 m n p)). Qed.
Lemma lem1033205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033206 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1033205) (@lem1033204 m n)). Qed.
Lemma lem1033207 (m : nat) : (term23 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1033206 m n)). Qed.
Lemma lem1033208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033209 (m : nat) : (term25 m) = (term26 m).
Proof. exact (MK_COMB (@lem1033208) (@lem1033207 m)). Qed.
Lemma lem1033210 : term27 = term28.
Proof. exact (fun_ext (fun m : nat => @lem1033209 m)). Qed.
Lemma lem1033211 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033212 : term29 = term30.
Proof. exact (MK_COMB (@lem1033211) (@lem1033210)). Qed.
Lemma lem1033213 : term30.
Proof. exact (EQ_MP (@lem1033212) (@lem77960)). Qed.
Lemma lem1033214 (m : nat) : term31 m.
Proof. exact (@lem1033213 m). Qed.
Lemma lem1033215 (m : nat) : (term31 m) = (term26 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1033216 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1033215 m) (@lem1033214 m)). Qed.
Lemma lem1033217 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1033216 m n). Qed.
Lemma lem1033218 (m : nat) (n : nat) : (term32 m n) = (term22 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1033219 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem1033218 m n) (@lem1033217 m n)). Qed.
Lemma lem1033220 (m : nat) (n : nat) (p : nat) : term33 m n p.
Proof. exact (@lem1033219 m n p). Qed.
Lemma lem1033221 (m : nat) (n : nat) (p : nat) : (term33 m n p) = ((term18 m n p) = (term14 m n p)).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem1033223 (m : nat) : term34 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1033224 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1033225 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem1033224 m) (@lem1033223 m)). Qed.
Lemma lem1033226 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem1033225 m n). Qed.
Lemma lem1033227 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1033228 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem1033227 m n) (@lem1033226 m n)). Qed.
Lemma lem1033229 (m : nat) (n : nat) (p : nat) : term38 m n p.
Proof. exact (@lem1033228 m n p). Qed.
Lemma lem1033230 (m : nat) (n : nat) (p : nat) : (term38 m n p) = ((term39 m n p) = (term40 m n p)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem1033232 (m : nat) : term41 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1033233 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1033234 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1033233 m) (@lem1033232 m)). Qed.
Lemma lem1033235 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem1033234 m n). Qed.
Lemma lem1033236 (n : nat) (m : nat) : (term43 m n) = (term44 n m).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem1033237 (n : nat) (m : nat) : term44 n m.
Proof. exact (EQ_MP (@lem1033236 n m) (@lem1033235 m n)). Qed.
Lemma lem1033238 (n : nat) (m : nat) (p : nat) : term45 n m p.
Proof. exact (@lem1033237 n m p). Qed.
Lemma lem1033239 (n : nat) (m : nat) (p : nat) : (term45 n m p) = ((term46 m n p) = (term47 n m p)).
Proof. exact (eq_refl (term45 n m p)). Qed.
Lemma lem1033241 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : term48 w x d y z e.
Proof. exact (h1). Qed.
Lemma lem1033249 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : w = (Nat.add x d).
Proof. exact (proj1 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033250 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1033251 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (Nat.mul w) = (term49 x d).
Proof. exact (MK_COMB (@lem1033250) (@lem1033249 w x d y z e h1)). Qed.
Lemma lem1033253 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : y = (Nat.add z e).
Proof. exact (proj2 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033254 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (Nat.mul w y) = (term50 x d z e).
Proof. exact (MK_COMB (@lem1033251 w x d y z e h1) (@lem1033253 w x d y z e h1)). Qed.
Lemma lem1033255 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1033256 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term51 w y) = (term52 x d z e).
Proof. exact (MK_COMB (@lem1033255) (@lem1033254 w x d y z e h1)). Qed.
Lemma lem1033257 (x : nat) (z : nat) : (Nat.mul x z) = (Nat.mul x z).
Proof. exact (eq_refl (Nat.mul x z)). Qed.
Lemma lem1033258 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term53 w y x z) = (term54 d e x z).
Proof. exact (MK_COMB (@lem1033256 w x d y z e h1) (@lem1033257 x z)). Qed.
Lemma lem1033259 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033260 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term55 w y x z) = (term56 d e x z).
Proof. exact (MK_COMB (@lem1033259) (@lem1033258 w x d y z e h1)). Qed.
Lemma lem1033262 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : w = (Nat.add x d).
Proof. exact (proj1 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033263 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1033264 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (Nat.mul w) = (term49 x d).
Proof. exact (MK_COMB (@lem1033263) (@lem1033262 w x d y z e h1)). Qed.
Lemma lem1033265 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1033266 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (Nat.mul w z) = (term39 x d z).
Proof. exact (MK_COMB (@lem1033264 w x d y z e h1) (@lem1033265 z)). Qed.
Lemma lem1033267 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1033268 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term51 w z) = (term57 x d z).
Proof. exact (MK_COMB (@lem1033267) (@lem1033266 w x d y z e h1)). Qed.
Lemma lem1033270 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : y = (Nat.add z e).
Proof. exact (proj2 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033271 (x : nat) : (Nat.mul x) = (Nat.mul x).
Proof. exact (eq_refl (Nat.mul x)). Qed.
Lemma lem1033272 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (Nat.mul x y) = (term46 x z e).
Proof. exact (MK_COMB (@lem1033271 x) (@lem1033270 w x d y z e h1)). Qed.
Lemma lem1033273 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term53 w z x y) = (term58 d x z e).
Proof. exact (MK_COMB (@lem1033268 w x d y z e h1) (@lem1033272 w x d y z e h1)). Qed.
Lemma lem1033274 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : ((term53 w y x z) = (term53 w z x y)) = ((term54 d e x z) = (term58 d x z e)).
Proof. exact (MK_COMB (@lem1033260 w x d y z e h1) (@lem1033273 w x d y z e h1)). Qed.
Lemma lem1033277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033278 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term59 w z x y) = (term60 d x z e).
Proof. exact (MK_COMB (@lem1033277) (@lem1033274 w x d y z e h1)). Qed.
Lemma lem1033284 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : w = (Nat.add x d).
Proof. exact (proj1 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033285 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033286 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (@eq nat w) = (term61 x d).
Proof. exact (MK_COMB (@lem1033285) (@lem1033284 w x d y z e h1)). Qed.
Lemma lem1033287 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1033288 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (w = x) = ((Nat.add x d) = x).
Proof. exact (MK_COMB (@lem1033286 w x d y z e h1) (@lem1033287 x)). Qed.
Lemma lem1033291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1033292 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term62 w x) = (term63 d x).
Proof. exact (MK_COMB (@lem1033291) (@lem1033288 w x d y z e h1)). Qed.
Lemma lem1033296 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : y = (Nat.add z e).
Proof. exact (proj2 (@lem1033241 w x d y z e h1)). Qed.
Lemma lem1033297 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033298 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (@eq nat y) = (term61 z e).
Proof. exact (MK_COMB (@lem1033297) (@lem1033296 w x d y z e h1)). Qed.
Lemma lem1033299 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1033300 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (y = z) = ((Nat.add z e) = z).
Proof. exact (MK_COMB (@lem1033298 w x d y z e h1) (@lem1033299 z)). Qed.
Lemma lem1033303 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (term64 w x y z) = (term65 d x e z).
Proof. exact (MK_COMB (@lem1033292 w x d y z e h1) (@lem1033300 w x d y z e h1)). Qed.
Lemma lem1033306 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term54 d e x z) = (term58 d x z e)) = (term65 d x e z)).
Proof. exact (MK_COMB (@lem1033278 w x d y z e h1) (@lem1033303 w x d y z e h1)). Qed.
Lemma lem1033309 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : (((term54 d e x z) = (term58 d x z e)) = (term65 d x e z)) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (SYM (@lem1033306 w x d y z e h1)). Qed.
Lemma lem1033315 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (EQ_MP (@lem1033230 m n p) (@lem1033229 m n p)). Qed.
Lemma lem1033316 (x : nat) (d : nat) (z : nat) (e : nat) : (term50 x d z e) = (term66 x d z e).
Proof. exact (@lem1033315 x d (Nat.add z e)). Qed.
Lemma lem1033318 (n : nat) (m : nat) (p : nat) : (term46 m n p) = (term47 n m p).
Proof. exact (EQ_MP (@lem1033239 n m p) (@lem1033238 n m p)). Qed.
Lemma lem1033319 (z : nat) (x : nat) (e : nat) : (term46 x z e) = (term47 z x e).
Proof. exact (@lem1033318 z x e). Qed.
Lemma lem1033320 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1033321 (z : nat) (x : nat) (e : nat) : (term67 x z e) = (term68 z x e).
Proof. exact (MK_COMB (@lem1033320) (@lem1033319 z x e)). Qed.
Lemma lem1033323 (n : nat) (m : nat) (p : nat) : (term46 m n p) = (term47 n m p).
Proof. exact (EQ_MP (@lem1033239 n m p) (@lem1033238 n m p)). Qed.
Lemma lem1033324 (z : nat) (d : nat) (e : nat) : (term46 d z e) = (term47 z d e).
Proof. exact (@lem1033323 z d e). Qed.
Lemma lem1033325 (x : nat) (z : nat) (d : nat) (e : nat) : (term66 x d z e) = (term69 x z d e).
Proof. exact (MK_COMB (@lem1033321 z x e) (@lem1033324 z d e)). Qed.
Lemma lem1033327 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1033221 m n p) (@lem1033220 m n p)). Qed.
Lemma lem1033328 (x : nat) (z : nat) (d : nat) (e : nat) : (term69 x z d e) = (term70 x z d e).
Proof. exact (@lem1033327 (Nat.mul x z) (Nat.mul x e) (term47 z d e)). Qed.
Lemma lem1033329 (x : nat) (z : nat) (d : nat) (e : nat) : (term66 x d z e) = (term70 x z d e).
Proof. exact (TRANS (@lem1033325 x z d e) (@lem1033328 x z d e)). Qed.
Lemma lem1033330 (x : nat) (z : nat) (d : nat) (e : nat) : (term50 x d z e) = (term70 x z d e).
Proof. exact (TRANS (@lem1033316 x d z e) (@lem1033329 x z d e)). Qed.
Lemma lem1033331 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1033332 (x : nat) (z : nat) (d : nat) (e : nat) : (term52 x d z e) = (term71 x z d e).
Proof. exact (MK_COMB (@lem1033331) (@lem1033330 x z d e)). Qed.
Lemma lem1033333 (x : nat) (z : nat) : (Nat.mul x z) = (Nat.mul x z).
Proof. exact (eq_refl (Nat.mul x z)). Qed.
Lemma lem1033334 (d : nat) (e : nat) (x : nat) (z : nat) : (term54 d e x z) = (term72 d e x z).
Proof. exact (MK_COMB (@lem1033332 x z d e) (@lem1033333 x z)). Qed.
Lemma lem1033336 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1033221 m n p) (@lem1033220 m n p)). Qed.
Lemma lem1033337 (d : nat) (e : nat) (x : nat) (z : nat) : (term72 d e x z) = (term73 d e x z).
Proof. exact (@lem1033336 (Nat.mul x z) (term74 x z d e) (Nat.mul x z)). Qed.
Lemma lem1033339 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1033221 m n p) (@lem1033220 m n p)). Qed.
Lemma lem1033340 (d : nat) (e : nat) (x : nat) (z : nat) : (term75 d e x z) = (term76 d e x z).
Proof. exact (@lem1033339 (Nat.mul x e) (term47 z d e) (Nat.mul x z)). Qed.
Lemma lem1033342 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1033221 m n p) (@lem1033220 m n p)). Qed.
Lemma lem1033343 (d : nat) (e : nat) (x : nat) (z : nat) : (term77 d e x z) = (term78 d e x z).
Proof. exact (@lem1033342 (Nat.mul d z) (Nat.mul d e) (Nat.mul x z)). Qed.
Lemma lem1033344 (x : nat) (e : nat) : (term51 x e) = (term51 x e).
Proof. exact (eq_refl (term51 x e)). Qed.
Lemma lem1033345 (d : nat) (e : nat) (x : nat) (z : nat) : (term76 d e x z) = (term79 d e x z).
Proof. exact (MK_COMB (@lem1033344 x e) (@lem1033343 d e x z)). Qed.
Lemma lem1033346 (d : nat) (e : nat) (x : nat) (z : nat) : (term75 d e x z) = (term79 d e x z).
Proof. exact (TRANS (@lem1033340 d e x z) (@lem1033345 d e x z)). Qed.
Lemma lem1033347 (x : nat) (z : nat) : (term51 x z) = (term51 x z).
Proof. exact (eq_refl (term51 x z)). Qed.
Lemma lem1033348 (d : nat) (e : nat) (x : nat) (z : nat) : (term73 d e x z) = (term80 d e x z).
Proof. exact (MK_COMB (@lem1033347 x z) (@lem1033346 d e x z)). Qed.
Lemma lem1033349 (d : nat) (e : nat) (x : nat) (z : nat) : (term72 d e x z) = (term80 d e x z).
Proof. exact (TRANS (@lem1033337 d e x z) (@lem1033348 d e x z)). Qed.
Lemma lem1033350 (d : nat) (e : nat) (x : nat) (z : nat) : (term54 d e x z) = (term80 d e x z).
Proof. exact (TRANS (@lem1033334 d e x z) (@lem1033349 d e x z)). Qed.
Lemma lem1033351 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033352 (d : nat) (e : nat) (x : nat) (z : nat) : (term56 d e x z) = (term81 d e x z).
Proof. exact (MK_COMB (@lem1033351) (@lem1033350 d e x z)). Qed.
Lemma lem1033354 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (EQ_MP (@lem1033230 m n p) (@lem1033229 m n p)). Qed.
Lemma lem1033355 (x : nat) (d : nat) (z : nat) : (term39 x d z) = (term40 x d z).
Proof. exact (@lem1033354 x d z). Qed.
Lemma lem1033356 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1033357 (x : nat) (d : nat) (z : nat) : (term57 x d z) = (term82 x d z).
Proof. exact (MK_COMB (@lem1033356) (@lem1033355 x d z)). Qed.
Lemma lem1033359 (n : nat) (m : nat) (p : nat) : (term46 m n p) = (term47 n m p).
Proof. exact (EQ_MP (@lem1033239 n m p) (@lem1033238 n m p)). Qed.
Lemma lem1033360 (z : nat) (x : nat) (e : nat) : (term46 x z e) = (term47 z x e).
Proof. exact (@lem1033359 z x e). Qed.
Lemma lem1033361 (d : nat) (z : nat) (x : nat) (e : nat) : (term58 d x z e) = (term83 d z x e).
Proof. exact (MK_COMB (@lem1033357 x d z) (@lem1033360 z x e)). Qed.
Lemma lem1033363 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1033221 m n p) (@lem1033220 m n p)). Qed.
Lemma lem1033364 (d : nat) (z : nat) (x : nat) (e : nat) : (term83 d z x e) = (term84 d z x e).
Proof. exact (@lem1033363 (Nat.mul x z) (Nat.mul d z) (term47 z x e)). Qed.
Lemma lem1033365 (d : nat) (z : nat) (x : nat) (e : nat) : (term58 d x z e) = (term84 d z x e).
Proof. exact (TRANS (@lem1033361 d z x e) (@lem1033364 d z x e)). Qed.
Lemma lem1033366 (d : nat) (z : nat) (x : nat) (e : nat) : ((term54 d e x z) = (term58 d x z e)) = ((term80 d e x z) = (term84 d z x e)).
Proof. exact (MK_COMB (@lem1033352 d e x z) (@lem1033365 d z x e)). Qed.
Lemma lem1033369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033370 (d : nat) (z : nat) (x : nat) (e : nat) : (term60 d x z e) = (term85 d z x e).
Proof. exact (MK_COMB (@lem1033369) (@lem1033366 d z x e)). Qed.
Lemma lem1033377 (d : nat) (x : nat) (e : nat) (z : nat) : (term65 d x e z) = (term65 d x e z).
Proof. exact (eq_refl (term65 d x e z)). Qed.
Lemma lem1033378 (d : nat) (x : nat) (e : nat) (z : nat) : (((term54 d e x z) = (term58 d x z e)) = (term65 d x e z)) = (((term80 d e x z) = (term84 d z x e)) = (term65 d x e z)).
Proof. exact (MK_COMB (@lem1033370 d z x e) (@lem1033377 d x e z)). Qed.
Lemma lem1033381 (d : nat) (x : nat) (e : nat) (z : nat) : (((term80 d e x z) = (term84 d z x e)) = (term65 d x e z)) = (((term54 d e x z) = (term58 d x z e)) = (term65 d x e z)).
Proof. exact (SYM (@lem1033378 d x e z)). Qed.
Lemma lem1033387 (a : nat) (c : nat) (e : nat) (b : nat) (d : nat) : (term16 a b c d e) = (term16 a c e b d).
Proof. exact (EQ_MP (@lem1033194 a c e b d) (@lem0)). Qed.
Lemma lem1033388 (z : nat) (x : nat) (d : nat) (e : nat) : (term80 d e x z) = (term86 z x d e).
Proof. exact (@lem1033387 (Nat.mul x z) (Nat.mul d z) (Nat.mul x z) (Nat.mul x e) (Nat.mul d e)). Qed.
Lemma lem1033389 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033390 (z : nat) (x : nat) (d : nat) (e : nat) : (term81 d e x z) = (term87 z x d e).
Proof. exact (MK_COMB (@lem1033389) (@lem1033388 z x d e)). Qed.
Lemma lem1033391 (d : nat) (z : nat) (x : nat) (e : nat) : (term84 d z x e) = (term84 d z x e).
Proof. exact (eq_refl (term84 d z x e)). Qed.
Lemma lem1033392 (d : nat) (z : nat) (x : nat) (e : nat) : ((term80 d e x z) = (term84 d z x e)) = ((term86 z x d e) = (term84 d z x e)).
Proof. exact (MK_COMB (@lem1033390 z x d e) (@lem1033391 d z x e)). Qed.
Lemma lem1033393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033394 (d : nat) (z : nat) (x : nat) (e : nat) : (term85 d z x e) = (term88 d z x e).
Proof. exact (MK_COMB (@lem1033393) (@lem1033392 d z x e)). Qed.
Lemma lem1033401 (d : nat) (x : nat) (e : nat) (z : nat) : (term65 d x e z) = (term65 d x e z).
Proof. exact (eq_refl (term65 d x e z)). Qed.
Lemma lem1033402 (d : nat) (x : nat) (e : nat) (z : nat) : (((term80 d e x z) = (term84 d z x e)) = (term65 d x e z)) = (((term86 z x d e) = (term84 d z x e)) = (term65 d x e z)).
Proof. exact (MK_COMB (@lem1033394 d z x e) (@lem1033401 d x e z)). Qed.
Lemma lem1033403 (d : nat) (x : nat) (e : nat) (z : nat) : (((term86 z x d e) = (term84 d z x e)) = (term65 d x e z)) = (((term80 d e x z) = (term84 d z x e)) = (term65 d x e z)).
Proof. exact (SYM (@lem1033402 d x e z)). Qed.
Lemma lem1033407 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1033090 m n p) (@lem1033089 m n p)). Qed.
Lemma lem1033408 (d : nat) (z : nat) (x : nat) (e : nat) : ((term86 z x d e) = (term84 d z x e)) = ((term89 z x d e) = (term90 d z x e)).
Proof. exact (@lem1033407 (Nat.mul x z) (term89 z x d e) (term90 d z x e)). Qed.
Lemma lem1033410 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1033090 m n p) (@lem1033089 m n p)). Qed.
Lemma lem1033411 (d : nat) (z : nat) (x : nat) (e : nat) : ((term89 z x d e) = (term90 d z x e)) = ((term91 z x d e) = (term47 z x e)).
Proof. exact (@lem1033410 (Nat.mul d z) (term91 z x d e) (term47 z x e)). Qed.
Lemma lem1033413 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1033090 m n p) (@lem1033089 m n p)). Qed.
Lemma lem1033414 (z : nat) (d : nat) (x : nat) (e : nat) : ((term91 z x d e) = (term47 z x e)) = ((term40 x d e) = (Nat.mul x e)).
Proof. exact (@lem1033413 (Nat.mul x z) (term40 x d e) (Nat.mul x e)). Qed.
Lemma lem1033416 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1033081 m n) (@lem1033080 m n)). Qed.
Lemma lem1033417 (x : nat) (d : nat) (e : nat) : ((term40 x d e) = (Nat.mul x e)) = ((Nat.mul d e) = (NUMERAL 0)).
Proof. exact (@lem1033416 (Nat.mul x e) (Nat.mul d e)). Qed.
Lemma lem1033419 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (EQ_MP (@lem1033075 m n) (@lem1033074 m n)). Qed.
Lemma lem1033420 (d : nat) (e : nat) : ((Nat.mul d e) = (NUMERAL 0)) = (term3 d e).
Proof. exact (@lem1033419 d e). Qed.
Lemma lem1033423 (x : nat) (d : nat) (e : nat) : ((term40 x d e) = (Nat.mul x e)) = (term3 d e).
Proof. exact (TRANS (@lem1033417 x d e) (@lem1033420 d e)). Qed.
Lemma lem1033424 (z : nat) (x : nat) (d : nat) (e : nat) : ((term91 z x d e) = (term47 z x e)) = (term3 d e).
Proof. exact (TRANS (@lem1033414 z d x e) (@lem1033423 x d e)). Qed.
Lemma lem1033425 (z : nat) (x : nat) (d : nat) (e : nat) : ((term89 z x d e) = (term90 d z x e)) = (term3 d e).
Proof. exact (TRANS (@lem1033411 d z x e) (@lem1033424 z x d e)). Qed.
Lemma lem1033426 (z : nat) (x : nat) (d : nat) (e : nat) : ((term86 z x d e) = (term84 d z x e)) = (term3 d e).
Proof. exact (TRANS (@lem1033408 d z x e) (@lem1033425 z x d e)). Qed.
Lemma lem1033431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033432 (z : nat) (x : nat) (d : nat) (e : nat) : (term88 d z x e) = (term92 d e).
Proof. exact (MK_COMB (@lem1033431) (@lem1033426 z x d e)). Qed.
Lemma lem1033436 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1033081 m n) (@lem1033080 m n)). Qed.
Lemma lem1033437 (x : nat) (d : nat) : ((Nat.add x d) = x) = (d = (NUMERAL 0)).
Proof. exact (@lem1033436 x d). Qed.
Lemma lem1033440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1033441 (x : nat) (d : nat) : (term63 d x) = (term93 d).
Proof. exact (MK_COMB (@lem1033440) (@lem1033437 x d)). Qed.
Lemma lem1033443 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1033081 m n) (@lem1033080 m n)). Qed.
Lemma lem1033444 (z : nat) (e : nat) : ((Nat.add z e) = z) = (e = (NUMERAL 0)).
Proof. exact (@lem1033443 z e). Qed.
Lemma lem1033447 (x : nat) (z : nat) (d : nat) (e : nat) : (term65 d x e z) = (term3 d e).
Proof. exact (MK_COMB (@lem1033441 x d) (@lem1033444 z e)). Qed.
Lemma lem1033450 (x : nat) (z : nat) (d : nat) (e : nat) : (((term86 z x d e) = (term84 d z x e)) = (term65 d x e z)) = ((term3 d e) = (term3 d e)).
Proof. exact (MK_COMB (@lem1033432 z x d e) (@lem1033447 x z d e)). Qed.
Lemma lem1033452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1033453 (x : Prop) : (x = x) = True.
Proof. exact (@lem1033452 Prop x). Qed.
Lemma lem1033454 (d : nat) (e : nat) : ((term3 d e) = (term3 d e)) = True.
Proof. exact (@lem1033453 (term3 d e)). Qed.
Lemma lem1033455 (d : nat) (x : nat) (e : nat) (z : nat) : (((term86 z x d e) = (term84 d z x e)) = (term65 d x e z)) = True.
Proof. exact (TRANS (@lem1033450 x z d e) (@lem1033454 d e)). Qed.
Lemma lem1033456 (d : nat) (x : nat) (e : nat) (z : nat) : True = (((term86 z x d e) = (term84 d z x e)) = (term65 d x e z)).
Proof. exact (SYM (@lem1033455 d x e z)). Qed.
Lemma lem1033457 (d : nat) (x : nat) (e : nat) (z : nat) : ((term86 z x d e) = (term84 d z x e)) = (term65 d x e z).
Proof. exact (EQ_MP (@lem1033456 d x e z) (@lem0)). Qed.
Lemma lem1033458 (d : nat) (x : nat) (e : nat) (z : nat) : ((term80 d e x z) = (term84 d z x e)) = (term65 d x e z).
Proof. exact (EQ_MP (@lem1033403 d x e z) (@lem1033457 d x e z)). Qed.
Lemma lem1033459 (d : nat) (x : nat) (e : nat) (z : nat) : ((term54 d e x z) = (term58 d x z e)) = (term65 d x e z).
Proof. exact (EQ_MP (@lem1033381 d x e z) (@lem1033458 d x e z)). Qed.
Lemma lem1033460 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) (h1 : term48 w x d y z e) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (EQ_MP (@lem1033309 w x d y z e h1) (@lem1033459 d x e z)). Qed.
Lemma lem1033461 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : term94 d e w x y z.
Proof. exact (fun h0 : term48 w x d y z e => @lem1033460 w x d y z e h0). Qed.
Lemma lem1033462 (t1 : Prop) : term95 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1033463 (t1 : Prop) : (term95 t1) = (term96 t1).
Proof. exact (eq_refl (term95 t1)). Qed.
Lemma lem1033464 (t1 : Prop) : term96 t1.
Proof. exact (EQ_MP (@lem1033463 t1) (@lem1033462 t1)). Qed.
Lemma lem1033465 (t1 : Prop) (t2 : Prop) : term97 t1 t2.
Proof. exact (@lem1033464 t1 t2). Qed.
Lemma lem1033466 (t1 : Prop) (t2 : Prop) : (term97 t1 t2) = (term98 t1 t2).
Proof. exact (eq_refl (term97 t1 t2)). Qed.
Lemma lem1033467 (t1 : Prop) (t2 : Prop) : term98 t1 t2.
Proof. exact (EQ_MP (@lem1033466 t1 t2) (@lem1033465 t1 t2)). Qed.
Lemma lem1033468 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term99 t1 t2 t3.
Proof. exact (@lem1033467 t1 t2 t3). Qed.
Lemma lem1033469 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term99 t1 t2 t3) = ((term100 t1 t2 t3) = (term101 t1 t2 t3)).
Proof. exact (eq_refl (term99 t1 t2 t3)). Qed.
Lemma lem1033470 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term100 t1 t2 t3) = (term101 t1 t2 t3).
Proof. exact (EQ_MP (@lem1033469 t1 t2 t3) (@lem1033468 t1 t2 t3)). Qed.
Lemma lem1033471 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term101 t1 t2 t3) = (term100 t1 t2 t3).
Proof. exact (SYM (@lem1033470 t1 t2 t3)). Qed.
Lemma lem1033472 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : term102 d e w x y.
Proof. exact (fun z : nat => @lem1033461 d e w x y z). Qed.
Lemma lem1033473 (d : nat) (e : nat) (w : nat) (x : nat) : term103 d e w x.
Proof. exact (fun y : nat => @lem1033472 d e w x y). Qed.
Lemma lem1033474 (d : nat) (e : nat) (w : nat) : term104 d e w.
Proof. exact (fun x : nat => @lem1033473 d e w x). Qed.
Lemma lem1033475 (d : nat) (e : nat) : term105 d e.
Proof. exact (fun w : nat => @lem1033474 d e w). Qed.
Lemma lem1033476 (d : nat) : term106 d.
Proof. exact (fun e : nat => @lem1033475 d e). Qed.
Lemma lem1033477 : term107.
Proof. exact (fun d : nat => @lem1033476 d). Qed.
Lemma lem1033478 (m : nat) : term108 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1033479 (m : nat) : (term108 m) = (term109 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem1033480 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem1033479 m) (@lem1033478 m)). Qed.
Lemma lem1033481 (m : nat) (n : nat) : term110 m n.
Proof. exact (@lem1033480 m n). Qed.
Lemma lem1033482 (n : nat) (m : nat) : (term110 m n) = ((Peano.le m n) = (term111 n m)).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem1033484 (y : nat) : term112 y.
Proof. exact (@lem96155 y). Qed.
Lemma lem1033485 (y : nat) : (term112 y) = (term113 y).
Proof. exact (eq_refl (term112 y)). Qed.
Lemma lem1033486 (y : nat) : term113 y.
Proof. exact (EQ_MP (@lem1033485 y) (@lem1033484 y)). Qed.
Lemma lem1033487 (y : nat) (z : nat) : term114 y z.
Proof. exact (@lem1033486 y z). Qed.
Lemma lem1033488 (z : nat) (y : nat) : (term114 y z) = (term115 z y).
Proof. exact (eq_refl (term114 y z)). Qed.
Lemma lem1033489 (z : nat) (y : nat) : term115 z y.
Proof. exact (EQ_MP (@lem1033488 z y) (@lem1033487 y z)). Qed.
Lemma lem1033490 (y : nat) (z : nat) (h1 : Peano.le y z) : Peano.le y z.
Proof. exact (h1). Qed.
Lemma lem1033491 (z : nat) (y : nat) (h1 : Peano.le z y) : Peano.le z y.
Proof. exact (h1). Qed.
Lemma lem1033492 (w : nat) : term112 w.
Proof. exact (@lem96155 w). Qed.
Lemma lem1033493 (w : nat) : (term112 w) = (term113 w).
Proof. exact (eq_refl (term112 w)). Qed.
Lemma lem1033494 (w : nat) : term113 w.
Proof. exact (EQ_MP (@lem1033493 w) (@lem1033492 w)). Qed.
Lemma lem1033495 (w : nat) (x : nat) : term114 w x.
Proof. exact (@lem1033494 w x). Qed.
Lemma lem1033496 (x : nat) (w : nat) : (term114 w x) = (term115 x w).
Proof. exact (eq_refl (term114 w x)). Qed.
Lemma lem1033497 (x : nat) (w : nat) : term115 x w.
Proof. exact (EQ_MP (@lem1033496 x w) (@lem1033495 w x)). Qed.
Lemma lem1033498 (w : nat) (x : nat) (h1 : Peano.le w x) : Peano.le w x.
Proof. exact (h1). Qed.
Lemma lem1033499 (x : nat) (w : nat) (h1 : Peano.le x w) : Peano.le x w.
Proof. exact (h1). Qed.
Lemma lem1033500 (m : nat) : term7 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1033501 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1033502 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1033501 m) (@lem1033500 m)). Qed.
Lemma lem1033503 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1033502 m n). Qed.
Lemma lem1033504 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1033505 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1033504 m n) (@lem1033503 m n)). Qed.
Lemma lem1033506 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1033505 m n p). Qed.
Lemma lem1033507 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1033539 : term116.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1033540 (n : nat) : term117 n.
Proof. exact (@lem1033539 n). Qed.
Lemma lem1033541 (n : nat) : (term117 n) = ((term118 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem1033552 (n : nat) : (term118 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1033541 n) (@lem1033540 n)). Qed.
Lemma lem1033553 (x : nat) : (term118 x) = (NUMERAL 0).
Proof. exact (@lem1033552 x). Qed.
Lemma lem1033554 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1033555 (x : nat) : (term119 x) = term120.
Proof. exact (MK_COMB (@lem1033554) (@lem1033553 x)). Qed.
Lemma lem1033556 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1033557 (x : nat) : ((term118 x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1033555 x) (@lem1033556)). Qed.
Lemma lem1033559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1033560 (x : nat) : (x = x) = True.
Proof. exact (@lem1033559 nat x). Qed.
Lemma lem1033561 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1033560 (NUMERAL 0)). Qed.
Lemma lem1033562 (x : nat) : ((term118 x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1033557 x) (@lem1033561)). Qed.
Lemma lem1033563 : term121 = term122.
Proof. exact (fun_ext (fun x : nat => @lem1033562 x)). Qed.
Lemma lem1033564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033565 : term116 = term123.
Proof. exact (MK_COMB (@lem1033564) (@lem1033563)). Qed.
Lemma lem1033567 {A : Type'} (t : Prop) : (term124 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1033568 (t : Prop) : (term125 t) = t.
Proof. exact (@lem1033567 nat t). Qed.
Lemma lem1033569 : term123 = True.
Proof. exact (@lem1033568 True). Qed.
Lemma lem1033570 : term116 = True.
Proof. exact (TRANS (@lem1033565) (@lem1033569)). Qed.
Lemma lem1033571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1033572 : term126 = (and True).
Proof. exact (MK_COMB (@lem1033571) (@lem1033570)). Qed.
Lemma lem1033590 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1033507 m n p) (@lem1033506 m n p)). Qed.
Lemma lem1033591 (x : nat) (y : nat) (z : nat) : ((Nat.add x y) = (Nat.add x z)) = (y = z).
Proof. exact (@lem1033590 x y z). Qed.
Lemma lem1033594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033595 (x : nat) (y : nat) (z : nat) : (term127 y x z) = (term128 y z).
Proof. exact (MK_COMB (@lem1033594) (@lem1033591 x y z)). Qed.
Lemma lem1033598 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1033599 (x : nat) (y : nat) (z : nat) : (((Nat.add x y) = (Nat.add x z)) = (y = z)) = ((y = z) = (y = z)).
Proof. exact (MK_COMB (@lem1033595 x y z) (@lem1033598 y z)). Qed.
Lemma lem1033601 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1033602 (x : Prop) : (x = x) = True.
Proof. exact (@lem1033601 Prop x). Qed.
Lemma lem1033603 (y : nat) (z : nat) : ((y = z) = (y = z)) = True.
Proof. exact (@lem1033602 (y = z)). Qed.
Lemma lem1033604 (x : nat) (y : nat) (z : nat) : (((Nat.add x y) = (Nat.add x z)) = (y = z)) = True.
Proof. exact (TRANS (@lem1033599 x y z) (@lem1033603 y z)). Qed.
Lemma lem1033605 (x : nat) (y : nat) : (term129 x y) = term122.
Proof. exact (fun_ext (fun z : nat => @lem1033604 x y z)). Qed.
Lemma lem1033606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033607 (x : nat) (y : nat) : (term10 x y) = term123.
Proof. exact (MK_COMB (@lem1033606) (@lem1033605 x y)). Qed.
Lemma lem1033609 {A : Type'} (t : Prop) : (term124 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1033610 (t : Prop) : (term125 t) = t.
Proof. exact (@lem1033609 nat t). Qed.
Lemma lem1033611 : term123 = True.
Proof. exact (@lem1033610 True). Qed.
Lemma lem1033612 (x : nat) (y : nat) : (term10 x y) = True.
Proof. exact (TRANS (@lem1033607 x y) (@lem1033611)). Qed.
Lemma lem1033613 (x : nat) : (term130 x) = term122.
Proof. exact (fun_ext (fun y : nat => @lem1033612 x y)). Qed.
Lemma lem1033614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033615 (x : nat) : (term8 x) = term123.
Proof. exact (MK_COMB (@lem1033614) (@lem1033613 x)). Qed.
Lemma lem1033617 {A : Type'} (t : Prop) : (term124 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1033618 (t : Prop) : (term125 t) = t.
Proof. exact (@lem1033617 nat t). Qed.
Lemma lem1033619 : term123 = True.
Proof. exact (@lem1033618 True). Qed.
Lemma lem1033620 (x : nat) : (term8 x) = True.
Proof. exact (TRANS (@lem1033615 x) (@lem1033619)). Qed.
Lemma lem1033621 : term131 = term122.
Proof. exact (fun_ext (fun x : nat => @lem1033620 x)). Qed.
Lemma lem1033622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1033623 : term132 = term123.
Proof. exact (MK_COMB (@lem1033622) (@lem1033621)). Qed.
Lemma lem1033625 {A : Type'} (t : Prop) : (term124 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1033626 (t : Prop) : (term125 t) = t.
Proof. exact (@lem1033625 nat t). Qed.
Lemma lem1033627 : term123 = True.
Proof. exact (@lem1033626 True). Qed.
Lemma lem1033628 : term132 = True.
Proof. exact (TRANS (@lem1033623) (@lem1033627)). Qed.
Lemma lem1033629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1033630 : term133 = (and True).
Proof. exact (MK_COMB (@lem1033629) (@lem1033628)). Qed.
Lemma lem1033659 : term134 = term134.
Proof. exact (eq_refl term134). Qed.
Lemma lem1033660 : term135 = term136.
Proof. exact (MK_COMB (@lem1033630) (@lem1033659)). Qed.
Lemma lem1033662 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1033663 : term136 = term134.
Proof. exact (@lem1033662 term134). Qed.
Lemma lem1033692 : term135 = term134.
Proof. exact (TRANS (@lem1033660) (@lem1033663)). Qed.
Lemma lem1033693 : term137 = term136.
Proof. exact (MK_COMB (@lem1033572) (@lem1033692)). Qed.
Lemma lem1033695 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1033696 : term136 = term134.
Proof. exact (@lem1033695 term134). Qed.
Lemma lem1033725 : term137 = term134.
Proof. exact (TRANS (@lem1033693) (@lem1033696)). Qed.
Lemma lem1033726 : term134 = term137.
Proof. exact (SYM (@lem1033725)). Qed.
Lemma lem1033728 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033729 (z : nat) (y : nat) : (Peano.le y z) = (term111 z y).
Proof. exact (@lem1033728 z y). Qed.
Lemma lem1033736 (y : nat) (z : nat) (h1 : Peano.le y z) : term111 z y.
Proof. exact (EQ_MP (@lem1033729 z y) (@lem1033490 y z h1)). Qed.
Lemma lem1033737 (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : z = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1033738 (w : nat) (x : nat) (y : nat) : (term138 w x y) = (term138 w x y).
Proof. exact (eq_refl (term138 w x y)). Qed.
Lemma lem1033739 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (term139 w x y z) = (term140 w x y d).
Proof. exact (MK_COMB (@lem1033738 w x y) (@lem1033737 z y d h1)). Qed.
Lemma lem1033740 (w : nat) (x : nat) (y : nat) (d : nat) : (term140 w x y d) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (term140 w x y d)). Qed.
Lemma lem1033741 (w : nat) (x : nat) (y : nat) (z : nat) : (term144 w x y z) = (term144 w x y z).
Proof. exact (eq_refl (term144 w x y z)). Qed.
Lemma lem1033742 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (term140 w x y d)) = ((term139 w x y z) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (MK_COMB (@lem1033741 w x y z) (@lem1033740 w x y d)). Qed.
Lemma lem1033743 (w : nat) (x : nat) (y : nat) (z : nat) : (term139 w x y z) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (eq_refl (term139 w x y z)). Qed.
Lemma lem1033744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033745 (w : nat) (x : nat) (y : nat) (z : nat) : (term144 w x y z) = (term145 w x y z).
Proof. exact (MK_COMB (@lem1033744) (@lem1033743 w x y z)). Qed.
Lemma lem1033746 (w : nat) (x : nat) (y : nat) (d : nat) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))). Qed.
Lemma lem1033747 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (MK_COMB (@lem1033745 w x y z) (@lem1033746 w x y d)). Qed.
Lemma lem1033748 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (term140 w x y d)) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (TRANS (@lem1033742 z w x y d) (@lem1033747 z w x y d)). Qed.
Lemma lem1033749 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (EQ_MP (@lem1033748 z w x y d) (@lem1033739 w x z y d h1)). Qed.
Lemma lem1033750 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (SYM (@lem1033749 w x z y d h1)). Qed.
Lemma lem1033752 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033753 (x : nat) (w : nat) : (Peano.le w x) = (term111 x w).
Proof. exact (@lem1033752 x w). Qed.
Lemma lem1033760 (w : nat) (x : nat) (h1 : Peano.le w x) : term111 x w.
Proof. exact (EQ_MP (@lem1033753 x w) (@lem1033498 w x h1)). Qed.
Lemma lem1033761 (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : x = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1033762 (w : nat) (y : nat) (d : nat) : (term146 w y d) = (term146 w y d).
Proof. exact (eq_refl (term146 w y d)). Qed.
Lemma lem1033763 (y : nat) (d : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (term147 w y d x) = (term148 y d w d').
Proof. exact (MK_COMB (@lem1033762 w y d) (@lem1033761 x w d' h1)). Qed.
Lemma lem1033764 (w : nat) (d' : nat) (y : nat) (d : nat) : (term148 y d w d') = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)).
Proof. exact (eq_refl (term148 y d w d')). Qed.
Lemma lem1033765 (w : nat) (y : nat) (d : nat) (x : nat) : (term152 w y d x) = (term152 w y d x).
Proof. exact (eq_refl (term152 w y d x)). Qed.
Lemma lem1033766 (x : nat) (w : nat) (d' : nat) (y : nat) (d : nat) : ((term147 w y d x) = (term148 y d w d')) = ((term147 w y d x) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))).
Proof. exact (MK_COMB (@lem1033765 w y d x) (@lem1033764 w d' y d)). Qed.
Lemma lem1033767 (w : nat) (x : nat) (y : nat) (d : nat) : (term147 w y d x) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (term147 w y d x)). Qed.
Lemma lem1033768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033769 (w : nat) (x : nat) (y : nat) (d : nat) : (term152 w y d x) = (term153 w x y d).
Proof. exact (MK_COMB (@lem1033768) (@lem1033767 w x y d)). Qed.
Lemma lem1033770 (w : nat) (d' : nat) (y : nat) (d : nat) : (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)).
Proof. exact (eq_refl (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))). Qed.
Lemma lem1033771 (x : nat) (w : nat) (d' : nat) (y : nat) (d : nat) : ((term147 w y d x) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))) = ((((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))).
Proof. exact (MK_COMB (@lem1033769 w x y d) (@lem1033770 w d' y d)). Qed.
Lemma lem1033772 (x : nat) (w : nat) (d' : nat) (y : nat) (d : nat) : ((term147 w y d x) = (term148 y d w d')) = ((((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))).
Proof. exact (TRANS (@lem1033766 x w d' y d) (@lem1033771 x w d' y d)). Qed.
Lemma lem1033773 (y : nat) (d : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)).
Proof. exact (EQ_MP (@lem1033772 x w d' y d) (@lem1033763 y d x w d' h1)). Qed.
Lemma lem1033774 (y : nat) (d : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (SYM (@lem1033773 y d x w d' h1)). Qed.
Lemma lem1033776 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033777 (y : nat) (z : nat) : (Peano.le z y) = (term111 y z).
Proof. exact (@lem1033776 y z). Qed.
Lemma lem1033784 (z : nat) (y : nat) (h1 : Peano.le z y) : term111 y z.
Proof. exact (EQ_MP (@lem1033777 y z) (@lem1033491 z y h1)). Qed.
Lemma lem1033785 (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : y = (Nat.add z d).
Proof. exact (h1). Qed.
Lemma lem1033786 (w : nat) (x : nat) (z : nat) : (term154 w x z) = (term154 w x z).
Proof. exact (eq_refl (term154 w x z)). Qed.
Lemma lem1033787 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (term155 w x z y) = (term156 w x z d).
Proof. exact (MK_COMB (@lem1033786 w x z) (@lem1033785 y z d h1)). Qed.
Lemma lem1033788 (w : nat) (x : nat) (d : nat) (z : nat) : (term156 w x z d) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (term156 w x z d)). Qed.
Lemma lem1033789 (w : nat) (x : nat) (z : nat) (y : nat) : (term158 w x z y) = (term158 w x z y).
Proof. exact (eq_refl (term158 w x z y)). Qed.
Lemma lem1033790 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (term156 w x z d)) = ((term155 w x z y) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (MK_COMB (@lem1033789 w x z y) (@lem1033788 w x d z)). Qed.
Lemma lem1033791 (w : nat) (x : nat) (y : nat) (z : nat) : (term155 w x z y) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (eq_refl (term155 w x z y)). Qed.
Lemma lem1033792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033793 (w : nat) (x : nat) (y : nat) (z : nat) : (term158 w x z y) = (term145 w x y z).
Proof. exact (MK_COMB (@lem1033792) (@lem1033791 w x y z)). Qed.
Lemma lem1033794 (w : nat) (x : nat) (d : nat) (z : nat) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))). Qed.
Lemma lem1033795 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (MK_COMB (@lem1033793 w x y z) (@lem1033794 w x d z)). Qed.
Lemma lem1033796 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (term156 w x z d)) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (TRANS (@lem1033790 y w x d z) (@lem1033795 y w x d z)). Qed.
Lemma lem1033797 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (EQ_MP (@lem1033796 y w x d z) (@lem1033787 w x y z d h1)). Qed.
Lemma lem1033798 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (SYM (@lem1033797 w x y z d h1)). Qed.
Lemma lem1033800 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033801 (x : nat) (w : nat) : (Peano.le w x) = (term111 x w).
Proof. exact (@lem1033800 x w). Qed.
Lemma lem1033808 (w : nat) (x : nat) (h1 : Peano.le w x) : term111 x w.
Proof. exact (EQ_MP (@lem1033801 x w) (@lem1033498 w x h1)). Qed.
Lemma lem1033809 (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : x = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1033810 (w : nat) (d : nat) (z : nat) : (term159 w d z) = (term159 w d z).
Proof. exact (eq_refl (term159 w d z)). Qed.
Lemma lem1033811 (d : nat) (z : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (term160 w d z x) = (term161 d z w d').
Proof. exact (MK_COMB (@lem1033810 w d z) (@lem1033809 x w d' h1)). Qed.
Lemma lem1033812 (w : nat) (d' : nat) (d : nat) (z : nat) : (term161 d z w d') = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)).
Proof. exact (eq_refl (term161 d z w d')). Qed.
Lemma lem1033813 (w : nat) (d : nat) (z : nat) (x : nat) : (term163 w d z x) = (term163 w d z x).
Proof. exact (eq_refl (term163 w d z x)). Qed.
Lemma lem1033814 (x : nat) (w : nat) (d' : nat) (d : nat) (z : nat) : ((term160 w d z x) = (term161 d z w d')) = ((term160 w d z x) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))).
Proof. exact (MK_COMB (@lem1033813 w d z x) (@lem1033812 w d' d z)). Qed.
Lemma lem1033815 (w : nat) (x : nat) (d : nat) (z : nat) : (term160 w d z x) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (term160 w d z x)). Qed.
Lemma lem1033816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033817 (w : nat) (x : nat) (d : nat) (z : nat) : (term163 w d z x) = (term164 w x d z).
Proof. exact (MK_COMB (@lem1033816) (@lem1033815 w x d z)). Qed.
Lemma lem1033818 (w : nat) (d' : nat) (d : nat) (z : nat) : (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)).
Proof. exact (eq_refl (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))). Qed.
Lemma lem1033819 (x : nat) (w : nat) (d' : nat) (d : nat) (z : nat) : ((term160 w d z x) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))) = ((((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))).
Proof. exact (MK_COMB (@lem1033817 w x d z) (@lem1033818 w d' d z)). Qed.
Lemma lem1033820 (x : nat) (w : nat) (d' : nat) (d : nat) (z : nat) : ((term160 w d z x) = (term161 d z w d')) = ((((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))).
Proof. exact (TRANS (@lem1033814 x w d' d z) (@lem1033819 x w d' d z)). Qed.
Lemma lem1033821 (d : nat) (z : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)).
Proof. exact (EQ_MP (@lem1033820 x w d' d z) (@lem1033811 d z x w d' h1)). Qed.
Lemma lem1033822 (d : nat) (z : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (SYM (@lem1033821 d z x w d' h1)). Qed.
Lemma lem1033824 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033825 (z : nat) (y : nat) : (Peano.le y z) = (term111 z y).
Proof. exact (@lem1033824 z y). Qed.
Lemma lem1033832 (y : nat) (z : nat) (h1 : Peano.le y z) : term111 z y.
Proof. exact (EQ_MP (@lem1033825 z y) (@lem1033490 y z h1)). Qed.
Lemma lem1033833 (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : z = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1033834 (w : nat) (x : nat) (y : nat) : (term138 w x y) = (term138 w x y).
Proof. exact (eq_refl (term138 w x y)). Qed.
Lemma lem1033835 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (term139 w x y z) = (term140 w x y d).
Proof. exact (MK_COMB (@lem1033834 w x y) (@lem1033833 z y d h1)). Qed.
Lemma lem1033836 (w : nat) (x : nat) (y : nat) (d : nat) : (term140 w x y d) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (term140 w x y d)). Qed.
Lemma lem1033837 (w : nat) (x : nat) (y : nat) (z : nat) : (term144 w x y z) = (term144 w x y z).
Proof. exact (eq_refl (term144 w x y z)). Qed.
Lemma lem1033838 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (term140 w x y d)) = ((term139 w x y z) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (MK_COMB (@lem1033837 w x y z) (@lem1033836 w x y d)). Qed.
Lemma lem1033839 (w : nat) (x : nat) (y : nat) (z : nat) : (term139 w x y z) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (eq_refl (term139 w x y z)). Qed.
Lemma lem1033840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033841 (w : nat) (x : nat) (y : nat) (z : nat) : (term144 w x y z) = (term145 w x y z).
Proof. exact (MK_COMB (@lem1033840) (@lem1033839 w x y z)). Qed.
Lemma lem1033842 (w : nat) (x : nat) (y : nat) (d : nat) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))). Qed.
Lemma lem1033843 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (MK_COMB (@lem1033841 w x y z) (@lem1033842 w x y d)). Qed.
Lemma lem1033844 (z : nat) (w : nat) (x : nat) (y : nat) (d : nat) : ((term139 w x y z) = (term140 w x y d)) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d))).
Proof. exact (TRANS (@lem1033838 z w x y d) (@lem1033843 z w x y d)). Qed.
Lemma lem1033845 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (EQ_MP (@lem1033844 z w x y d) (@lem1033835 w x z y d h1)). Qed.
Lemma lem1033846 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : z = (Nat.add y d)) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (SYM (@lem1033845 w x z y d h1)). Qed.
Lemma lem1033848 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033849 (w : nat) (x : nat) : (Peano.le x w) = (term111 w x).
Proof. exact (@lem1033848 w x). Qed.
Lemma lem1033856 (x : nat) (w : nat) (h1 : Peano.le x w) : term111 w x.
Proof. exact (EQ_MP (@lem1033849 w x) (@lem1033499 x w h1)). Qed.
Lemma lem1033857 (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : w = (Nat.add x d').
Proof. exact (h1). Qed.
Lemma lem1033858 (x : nat) (y : nat) (d : nat) : (term165 x y d) = (term165 x y d).
Proof. exact (eq_refl (term165 x y d)). Qed.
Lemma lem1033859 (y : nat) (d : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (term166 x y d w) = (term167 y d x d').
Proof. exact (MK_COMB (@lem1033858 x y d) (@lem1033857 w x d' h1)). Qed.
Lemma lem1033860 (d' : nat) (x : nat) (y : nat) (d : nat) : (term167 y d x d') = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)).
Proof. exact (eq_refl (term167 y d x d')). Qed.
Lemma lem1033861 (x : nat) (y : nat) (d : nat) (w : nat) : (term169 x y d w) = (term169 x y d w).
Proof. exact (eq_refl (term169 x y d w)). Qed.
Lemma lem1033862 (w : nat) (d' : nat) (x : nat) (y : nat) (d : nat) : ((term166 x y d w) = (term167 y d x d')) = ((term166 x y d w) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))).
Proof. exact (MK_COMB (@lem1033861 x y d w) (@lem1033860 d' x y d)). Qed.
Lemma lem1033863 (w : nat) (x : nat) (y : nat) (d : nat) : (term166 x y d w) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (eq_refl (term166 x y d w)). Qed.
Lemma lem1033864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033865 (w : nat) (x : nat) (y : nat) (d : nat) : (term169 x y d w) = (term153 w x y d).
Proof. exact (MK_COMB (@lem1033864) (@lem1033863 w x y d)). Qed.
Lemma lem1033866 (d' : nat) (x : nat) (y : nat) (d : nat) : (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)).
Proof. exact (eq_refl (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))). Qed.
Lemma lem1033867 (w : nat) (d' : nat) (x : nat) (y : nat) (d : nat) : ((term166 x y d w) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))) = ((((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))).
Proof. exact (MK_COMB (@lem1033865 w x y d) (@lem1033866 d' x y d)). Qed.
Lemma lem1033868 (w : nat) (d' : nat) (x : nat) (y : nat) (d : nat) : ((term166 x y d w) = (term167 y d x d')) = ((((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))).
Proof. exact (TRANS (@lem1033862 w d' x y d) (@lem1033867 w d' x y d)). Qed.
Lemma lem1033869 (y : nat) (d : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)).
Proof. exact (EQ_MP (@lem1033868 w d' x y d) (@lem1033859 y d w x d' h1)). Qed.
Lemma lem1033870 (y : nat) (d : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)) = (((term141 w x y d) = (term142 w d x y)) = (term143 w x y d)).
Proof. exact (SYM (@lem1033869 y d w x d' h1)). Qed.
Lemma lem1033872 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033873 (y : nat) (z : nat) : (Peano.le z y) = (term111 y z).
Proof. exact (@lem1033872 y z). Qed.
Lemma lem1033880 (z : nat) (y : nat) (h1 : Peano.le z y) : term111 y z.
Proof. exact (EQ_MP (@lem1033873 y z) (@lem1033491 z y h1)). Qed.
Lemma lem1033881 (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : y = (Nat.add z d).
Proof. exact (h1). Qed.
Lemma lem1033882 (w : nat) (x : nat) (z : nat) : (term154 w x z) = (term154 w x z).
Proof. exact (eq_refl (term154 w x z)). Qed.
Lemma lem1033883 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (term155 w x z y) = (term156 w x z d).
Proof. exact (MK_COMB (@lem1033882 w x z) (@lem1033881 y z d h1)). Qed.
Lemma lem1033884 (w : nat) (x : nat) (d : nat) (z : nat) : (term156 w x z d) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (term156 w x z d)). Qed.
Lemma lem1033885 (w : nat) (x : nat) (z : nat) (y : nat) : (term158 w x z y) = (term158 w x z y).
Proof. exact (eq_refl (term158 w x z y)). Qed.
Lemma lem1033886 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (term156 w x z d)) = ((term155 w x z y) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (MK_COMB (@lem1033885 w x z y) (@lem1033884 w x d z)). Qed.
Lemma lem1033887 (w : nat) (x : nat) (y : nat) (z : nat) : (term155 w x z y) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (eq_refl (term155 w x z y)). Qed.
Lemma lem1033888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033889 (w : nat) (x : nat) (y : nat) (z : nat) : (term158 w x z y) = (term145 w x y z).
Proof. exact (MK_COMB (@lem1033888) (@lem1033887 w x y z)). Qed.
Lemma lem1033890 (w : nat) (x : nat) (d : nat) (z : nat) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))). Qed.
Lemma lem1033891 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (MK_COMB (@lem1033889 w x y z) (@lem1033890 w x d z)). Qed.
Lemma lem1033892 (y : nat) (w : nat) (x : nat) (d : nat) (z : nat) : ((term155 w x z y) = (term156 w x z d)) = ((((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z))).
Proof. exact (TRANS (@lem1033886 y w x d z) (@lem1033891 y w x d z)). Qed.
Lemma lem1033893 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (EQ_MP (@lem1033892 y w x d z) (@lem1033883 w x y z d h1)). Qed.
Lemma lem1033894 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : y = (Nat.add z d)) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)).
Proof. exact (SYM (@lem1033893 w x y z d h1)). Qed.
Lemma lem1033896 (n : nat) (m : nat) : (Peano.le m n) = (term111 n m).
Proof. exact (EQ_MP (@lem1033482 n m) (@lem1033481 m n)). Qed.
Lemma lem1033897 (w : nat) (x : nat) : (Peano.le x w) = (term111 w x).
Proof. exact (@lem1033896 w x). Qed.
Lemma lem1033904 (x : nat) (w : nat) (h1 : Peano.le x w) : term111 w x.
Proof. exact (EQ_MP (@lem1033897 w x) (@lem1033499 x w h1)). Qed.
Lemma lem1033905 (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : w = (Nat.add x d').
Proof. exact (h1). Qed.
Lemma lem1033906 (x : nat) (d : nat) (z : nat) : (term170 x d z) = (term170 x d z).
Proof. exact (eq_refl (term170 x d z)). Qed.
Lemma lem1033907 (d : nat) (z : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (term171 x d z w) = (term172 d z x d').
Proof. exact (MK_COMB (@lem1033906 x d z) (@lem1033905 w x d' h1)). Qed.
Lemma lem1033908 (d' : nat) (x : nat) (d : nat) (z : nat) : (term172 d z x d') = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)).
Proof. exact (eq_refl (term172 d z x d')). Qed.
Lemma lem1033909 (x : nat) (d : nat) (z : nat) (w : nat) : (term173 x d z w) = (term173 x d z w).
Proof. exact (eq_refl (term173 x d z w)). Qed.
Lemma lem1033910 (w : nat) (d' : nat) (x : nat) (d : nat) (z : nat) : ((term171 x d z w) = (term172 d z x d')) = ((term171 x d z w) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))).
Proof. exact (MK_COMB (@lem1033909 x d z w) (@lem1033908 d' x d z)). Qed.
Lemma lem1033911 (w : nat) (x : nat) (d : nat) (z : nat) : (term171 x d z w) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (eq_refl (term171 x d z w)). Qed.
Lemma lem1033912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1033913 (w : nat) (x : nat) (d : nat) (z : nat) : (term173 x d z w) = (term164 w x d z).
Proof. exact (MK_COMB (@lem1033912) (@lem1033911 w x d z)). Qed.
Lemma lem1033914 (d' : nat) (x : nat) (d : nat) (z : nat) : (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)).
Proof. exact (eq_refl (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))). Qed.
Lemma lem1033915 (w : nat) (d' : nat) (x : nat) (d : nat) (z : nat) : ((term171 x d z w) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))) = ((((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))).
Proof. exact (MK_COMB (@lem1033913 w x d z) (@lem1033914 d' x d z)). Qed.
Lemma lem1033916 (w : nat) (d' : nat) (x : nat) (d : nat) (z : nat) : ((term171 x d z w) = (term172 d z x d')) = ((((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))).
Proof. exact (TRANS (@lem1033910 w d' x d z) (@lem1033915 w d' x d z)). Qed.
Lemma lem1033917 (d : nat) (z : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)).
Proof. exact (EQ_MP (@lem1033916 w d' x d z) (@lem1033907 d z w x d' h1)). Qed.
Lemma lem1033918 (d : nat) (z : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)) = (((term142 w d x z) = (term141 w x z d)) = (term157 w x d z)).
Proof. exact (SYM (@lem1033917 d z w x d' h1)). Qed.
Lemma lem1033920 (p : Prop) : p = (term174 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1033921 (w : nat) (d' : nat) (y : nat) (d : nat) : (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)) = (term175 w d' y d).
Proof. exact (@lem1033920 (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d))). Qed.
Lemma lem1033922 (w : nat) (d' : nat) (y : nat) (d : nat) : (term175 w d' y d) = (((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d)).
Proof. exact (SYM (@lem1033921 w d' y d)). Qed.
Lemma lem1033923 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term176 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1033926 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term177 w d' y d) : term177 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1033927 (w : nat) (d' : nat) (y : nat) (d : nat) : term178 w d' y d.
Proof. exact (fun h0 : term177 w d' y d => @lem1033926 w d' y d h0). Qed.
Lemma lem1033928 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term178 w d' y d) : term178 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1033929 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term177 w d' y d) : term177 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1033930 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term177 w d' y d) (h2 : term178 w d' y d) : term177 w d' y d.
Proof. exact (@lem1033928 w d' y d h2 (@lem1033929 w d' y d h1)). Qed.
Lemma lem1033931 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term177 w d' y d) : term179 w d' y d.
Proof. exact (fun h0 : term178 w d' y d => @lem1033930 w d' y d h1 h0). Qed.
Lemma lem1033932 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term178 w d' y d) : term178 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1033933 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term177 w d' y d) (h2 : term178 w d' y d) : term177 w d' y d.
Proof. exact (@lem1033931 w d' y d h1 (@lem1033932 w d' y d h2)). Qed.
Lemma lem1033934 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term178 w d' y d) : term178 w d' y d.
Proof. exact (fun h0 : term177 w d' y d => @lem1033933 w d' y d h0 h1). Qed.
Lemma lem1033935 (w : nat) (d' : nat) (y : nat) (d : nat) : term180 w d' y d.
Proof. exact (fun h0 : term178 w d' y d => @lem1033934 w d' y d h0). Qed.
Lemma lem1033938 (w : nat) (d' : nat) (y : nat) (d : nat) : term178 w d' y d.
Proof. exact (@lem1033935 w d' y d (@lem1033927 w d' y d)). Qed.
Lemma lem1033980 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1033981 : term181 = term182.
Proof. exact (@lem1033980 term107). Qed.
Lemma lem1034012 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1034013 : term184 = term185.
Proof. exact (MK_COMB (@lem1034012) (@lem1033981)). Qed.
Lemma lem1034016 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem1034017 : term187 = term188.
Proof. exact (MK_COMB (@lem1034016) (@lem1034013)). Qed.
Lemma lem1034020 (w : nat) (d' : nat) (y : nat) (d : nat) : (term189 w d' y d) = (term189 w d' y d).
Proof. exact (eq_refl (term189 w d' y d)). Qed.
Lemma lem1034021 (w : nat) (d' : nat) (y : nat) (d : nat) : (term177 w d' y d) = (term190 w d' y d).
Proof. exact (MK_COMB (@lem1034020 w d' y d) (@lem1034017)). Qed.
Lemma lem1034024 (d' : nat) (y : nat) (d : nat) : (term191 d' y d) = (term192 d' y d).
Proof. exact (fun_ext (fun w : nat => @lem1034021 w d' y d)). Qed.
Lemma lem1034025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034026 (d' : nat) (y : nat) (d : nat) : (term193 d' y d) = (term194 d' y d).
Proof. exact (MK_COMB (@lem1034025) (@lem1034024 d' y d)). Qed.
Lemma lem1034031 (y : nat) (d : nat) : (term195 y d) = (term196 y d).
Proof. exact (fun_ext (fun d' : nat => @lem1034026 d' y d)). Qed.
Lemma lem1034032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034033 (y : nat) (d : nat) : (term197 y d) = (term198 y d).
Proof. exact (MK_COMB (@lem1034032) (@lem1034031 y d)). Qed.
Lemma lem1034038 (d : nat) : (term199 d) = (term200 d).
Proof. exact (fun_ext (fun y : nat => @lem1034033 y d)). Qed.
Lemma lem1034039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034040 (d : nat) : (term201 d) = (term202 d).
Proof. exact (MK_COMB (@lem1034039) (@lem1034038 d)). Qed.
Lemma lem1034045 : term203 = term204.
Proof. exact (fun_ext (fun d : nat => @lem1034040 d)). Qed.
Lemma lem1034046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034055 : term205 = term206.
Proof. exact (MK_COMB (@lem1034046) (@lem1034045)). Qed.
Lemma lem1034072 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term94 d e w x y z).
Proof. exact (eq_refl (term94 d e w x y z)). Qed.
Lemma lem1034073 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term207 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1034072 d e w x y z)). Qed.
Lemma lem1034074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034075 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term102 d e w x y).
Proof. exact (MK_COMB (@lem1034074) (@lem1034073 d e w x y)). Qed.
Lemma lem1034076 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term208 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1034075 d e w x y)). Qed.
Lemma lem1034077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034078 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term103 d e w x).
Proof. exact (MK_COMB (@lem1034077) (@lem1034076 d e w x)). Qed.
Lemma lem1034079 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term209 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1034078 d e w x)). Qed.
Lemma lem1034080 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034081 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term104 d e w).
Proof. exact (MK_COMB (@lem1034080) (@lem1034079 d e w)). Qed.
Lemma lem1034082 (d : nat) (e : nat) : (term210 d e) = (term210 d e).
Proof. exact (fun_ext (fun w : nat => @lem1034081 d e w)). Qed.
Lemma lem1034083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034084 (d : nat) (e : nat) : (term105 d e) = (term105 d e).
Proof. exact (MK_COMB (@lem1034083) (@lem1034082 d e)). Qed.
Lemma lem1034085 (d : nat) : (term211 d) = (term211 d).
Proof. exact (fun_ext (fun e : nat => @lem1034084 d e)). Qed.
Lemma lem1034086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034087 (d : nat) : (term106 d) = (term106 d).
Proof. exact (MK_COMB (@lem1034086) (@lem1034085 d)). Qed.
Lemma lem1034088 : term212 = term212.
Proof. exact (fun_ext (fun d : nat => @lem1034087 d)). Qed.
Lemma lem1034089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034090 : term107 = term107.
Proof. exact (MK_COMB (@lem1034089) (@lem1034088)). Qed.
Lemma lem1034091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1034092 : term182 = term182.
Proof. exact (MK_COMB (@lem1034091) (@lem1034090)). Qed.
Lemma lem1034093 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1034094 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1034093 n m)). Qed.
Lemma lem1034095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034096 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1034095) (@lem1034094 m)). Qed.
Lemma lem1034097 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1034096 m)). Qed.
Lemma lem1034098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034099 : term216 = term216.
Proof. exact (MK_COMB (@lem1034098) (@lem1034097)). Qed.
Lemma lem1034100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1034101 : term183 = term183.
Proof. exact (MK_COMB (@lem1034100) (@lem1034099)). Qed.
Lemma lem1034102 : term185 = term185.
Proof. exact (MK_COMB (@lem1034101) (@lem1034092)). Qed.
Lemma lem1034103 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1034104 (m : nat) : (term217 m) = (term217 m).
Proof. exact (fun_ext (fun n : nat => @lem1034103 n m)). Qed.
Lemma lem1034105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034106 (m : nat) : (term218 m) = (term218 m).
Proof. exact (MK_COMB (@lem1034105) (@lem1034104 m)). Qed.
Lemma lem1034107 : term219 = term219.
Proof. exact (fun_ext (fun m : nat => @lem1034106 m)). Qed.
Lemma lem1034108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034109 : term220 = term220.
Proof. exact (MK_COMB (@lem1034108) (@lem1034107)). Qed.
Lemma lem1034110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1034111 : term186 = term186.
Proof. exact (MK_COMB (@lem1034110) (@lem1034109)). Qed.
Lemma lem1034112 : term188 = term188.
Proof. exact (MK_COMB (@lem1034111) (@lem1034102)). Qed.
Lemma lem1034125 (w : nat) (d' : nat) (y : nat) (d : nat) : (term189 w d' y d) = (term189 w d' y d).
Proof. exact (eq_refl (term189 w d' y d)). Qed.
Lemma lem1034126 (w : nat) (d' : nat) (y : nat) (d : nat) : (term190 w d' y d) = (term190 w d' y d).
Proof. exact (MK_COMB (@lem1034125 w d' y d) (@lem1034112)). Qed.
Lemma lem1034127 (d' : nat) (y : nat) (d : nat) : (term192 d' y d) = (term192 d' y d).
Proof. exact (fun_ext (fun w : nat => @lem1034126 w d' y d)). Qed.
Lemma lem1034128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034129 (d' : nat) (y : nat) (d : nat) : (term194 d' y d) = (term194 d' y d).
Proof. exact (MK_COMB (@lem1034128) (@lem1034127 d' y d)). Qed.
Lemma lem1034130 (y : nat) (d : nat) : (term196 y d) = (term196 y d).
Proof. exact (fun_ext (fun d' : nat => @lem1034129 d' y d)). Qed.
Lemma lem1034131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034132 (y : nat) (d : nat) : (term198 y d) = (term198 y d).
Proof. exact (MK_COMB (@lem1034131) (@lem1034130 y d)). Qed.
Lemma lem1034133 (d : nat) : (term200 d) = (term200 d).
Proof. exact (fun_ext (fun y : nat => @lem1034132 y d)). Qed.
Lemma lem1034134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034135 (d : nat) : (term202 d) = (term202 d).
Proof. exact (MK_COMB (@lem1034134) (@lem1034133 d)). Qed.
Lemma lem1034136 : term204 = term204.
Proof. exact (fun_ext (fun d : nat => @lem1034135 d)). Qed.
Lemma lem1034137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034138 : term206 = term206.
Proof. exact (MK_COMB (@lem1034137) (@lem1034136)). Qed.
Lemma lem1034239 : term205 = term206.
Proof. exact (TRANS (@lem1034055) (@lem1034138)). Qed.
Lemma lem1034240 : term206 = term205.
Proof. exact (SYM (@lem1034239)). Qed.
Lemma lem1034241 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term176 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1034243 (h1 : term216) : term216.
Proof. exact (h1). Qed.
Lemma lem1034244 (h1 : term107) : term107.
Proof. exact (h1). Qed.
Lemma lem1034255 (w : nat) (d' : nat) (y : nat) (d : nat) : (term221 w d' y d) = (term222 w d' y d).
Proof. exact (@lem17160 (w = (Nat.add w d')) (y = (Nat.add y d))). Qed.
Lemma lem1034261 (w : nat) (d' : nat) (y : nat) (d : nat) : (term223 w d' y d) = (term223 w d' y d).
Proof. exact (eq_refl (term223 w d' y d)). Qed.
Lemma lem1034263 (d : nat) (w : nat) (d' : nat) (y : nat) : (term224 d w d' y) = (term224 d w d' y).
Proof. exact (eq_refl (term224 d w d' y)). Qed.
Lemma lem1034264 (w : nat) (d' : nat) (y : nat) (d : nat) : (term225 w d' y d) = (term226 w d' y d).
Proof. exact (MK_COMB (@lem1034263 d w d' y) (@lem1034255 w d' y d)). Qed.
Lemma lem1034265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1034266 (w : nat) (d' : nat) (y : nat) (d : nat) : (term227 w d' y d) = (term228 w d' y d).
Proof. exact (MK_COMB (@lem1034265) (@lem1034264 w d' y d)). Qed.
Lemma lem1034267 (w : nat) (d' : nat) (y : nat) (d : nat) : (term229 w d' y d) = (term230 w d' y d).
Proof. exact (MK_COMB (@lem1034266 w d' y d) (@lem1034261 w d' y d)). Qed.
Lemma lem1034268 (w : nat) (d' : nat) (y : nat) (d : nat) : (term176 w d' y d) = (term229 w d' y d).
Proof. exact (@lem17646 ((term149 w d' y d) = (term150 d w d' y)) (term151 w d' y d)). Qed.
Lemma lem1034273 (w : nat) (d' : nat) (y : nat) (d : nat) : (term176 w d' y d) = (term230 w d' y d).
Proof. exact (TRANS (@lem1034268 w d' y d) (@lem1034267 w d' y d)). Qed.
Lemma lem1034295 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1034296 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1034295 n m)). Qed.
Lemma lem1034297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034298 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1034297) (@lem1034296 m)). Qed.
Lemma lem1034299 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1034298 m)). Qed.
Lemma lem1034300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034313 : term216 = term216.
Proof. exact (MK_COMB (@lem1034300) (@lem1034299)). Qed.
Lemma lem1034314 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1034313) (@lem1034243 h1)). Qed.
Lemma lem1034321 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term231 w x d y z e) = (term232 w x d y z e).
Proof. exact (@lem17045 (w = (Nat.add x d)) (y = (Nat.add z e))). Qed.
Lemma lem1034332 (w : nat) (x : nat) (y : nat) (z : nat) : (term233 w x y z) = (term234 w x y z).
Proof. exact (@lem17160 (w = x) (y = z)). Qed.
Lemma lem1034338 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1034340 (w : nat) (z : nat) (x : nat) (y : nat) : (term236 w z x y) = (term236 w z x y).
Proof. exact (eq_refl (term236 w z x y)). Qed.
Lemma lem1034341 (w : nat) (x : nat) (y : nat) (z : nat) : (term237 w x y z) = (term238 w x y z).
Proof. exact (MK_COMB (@lem1034340 w z x y) (@lem1034332 w x y z)). Qed.
Lemma lem1034342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1034343 (w : nat) (x : nat) (y : nat) (z : nat) : (term239 w x y z) = (term240 w x y z).
Proof. exact (MK_COMB (@lem1034342) (@lem1034341 w x y z)). Qed.
Lemma lem1034344 (w : nat) (x : nat) (y : nat) (z : nat) : (term241 w x y z) = (term242 w x y z).
Proof. exact (MK_COMB (@lem1034343 w x y z) (@lem1034338 w x y z)). Qed.
Lemma lem1034345 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term241 w x y z).
Proof. exact (@lem17784 ((term53 w y x z) = (term53 w z x y)) (term64 w x y z)). Qed.
Lemma lem1034346 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term242 w x y z).
Proof. exact (TRANS (@lem1034345 w x y z) (@lem1034344 w x y z)). Qed.
Lemma lem1034347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1034348 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term243 w x d y z e) = (term244 w x d y z e).
Proof. exact (MK_COMB (@lem1034347) (@lem1034321 w x d y z e)). Qed.
Lemma lem1034349 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term245 d e w x y z) = (term246 d e w x y z).
Proof. exact (MK_COMB (@lem1034348 w x d y z e) (@lem1034346 w x y z)). Qed.
Lemma lem1034350 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term245 d e w x y z).
Proof. exact (@lem17265 (term48 w x d y z e) (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z))). Qed.
Lemma lem1034351 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term246 d e w x y z).
Proof. exact (TRANS (@lem1034350 d e w x y z) (@lem1034349 d e w x y z)). Qed.
Lemma lem1034352 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1034351 d e w x y z)). Qed.
Lemma lem1034353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034354 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1034353) (@lem1034352 d e w x y)). Qed.
Lemma lem1034355 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1034354 d e w x y)). Qed.
Lemma lem1034356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034357 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1034356) (@lem1034355 d e w x)). Qed.
Lemma lem1034358 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1034357 d e w x)). Qed.
Lemma lem1034359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034360 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1034359) (@lem1034358 d e w)). Qed.
Lemma lem1034361 (d : nat) (e : nat) : (term210 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1034360 d e w)). Qed.
Lemma lem1034362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034363 (d : nat) (e : nat) : (term105 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1034362) (@lem1034361 d e)). Qed.
Lemma lem1034364 (d : nat) : (term211 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1034363 d e)). Qed.
Lemma lem1034365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034366 (d : nat) : (term106 d) = (term256 d).
Proof. exact (MK_COMB (@lem1034365) (@lem1034364 d)). Qed.
Lemma lem1034367 : term212 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1034366 d)). Qed.
Lemma lem1034368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034441 : term107 = term258.
Proof. exact (MK_COMB (@lem1034368) (@lem1034367)). Qed.
Lemma lem1034442 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1034441) (@lem1034244 h1)). Qed.
Lemma lem1034590 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term230 w d' y d.
Proof. exact (EQ_MP (@lem1034273 w d' y d) (@lem1034241 w d' y d h1)). Qed.
Lemma lem1034623 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1034624 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1034623 n m)). Qed.
Lemma lem1034625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034626 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1034625) (@lem1034624 m)). Qed.
Lemma lem1034627 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1034626 m)). Qed.
Lemma lem1034628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034629 : term216 = term216.
Proof. exact (MK_COMB (@lem1034628) (@lem1034627)). Qed.
Lemma lem1034630 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1034629) (@lem1034314 h1)). Qed.
Lemma lem1034757 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term246 d e w x y z).
Proof. exact (eq_refl (term246 d e w x y z)). Qed.
Lemma lem1034758 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1034757 d e w x y z)). Qed.
Lemma lem1034759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034760 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1034759) (@lem1034758 d e w x y)). Qed.
Lemma lem1034761 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1034760 d e w x y)). Qed.
Lemma lem1034762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034763 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1034762) (@lem1034761 d e w x)). Qed.
Lemma lem1034764 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1034763 d e w x)). Qed.
Lemma lem1034765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034766 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1034765) (@lem1034764 d e w)). Qed.
Lemma lem1034767 (d : nat) (e : nat) : (term253 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1034766 d e w)). Qed.
Lemma lem1034768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034769 (d : nat) (e : nat) : (term254 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1034768) (@lem1034767 d e)). Qed.
Lemma lem1034770 (d : nat) : (term255 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1034769 d e)). Qed.
Lemma lem1034771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034772 (d : nat) : (term256 d) = (term256 d).
Proof. exact (MK_COMB (@lem1034771) (@lem1034770 d)). Qed.
Lemma lem1034773 : term257 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1034772 d)). Qed.
Lemma lem1034774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034775 : term258 = term258.
Proof. exact (MK_COMB (@lem1034774) (@lem1034773)). Qed.
Lemma lem1034776 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1034775) (@lem1034442 h1)). Qed.
Lemma lem1034777 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term226 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1034778 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term223 w d' y d.
Proof. exact (h1). Qed.
Lemma lem1034779 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term222 w d' y d.
Proof. exact (proj2 (@lem1034777 w d' y d h1)). Qed.
Lemma lem1034783 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term151 w d' y d.
Proof. exact (proj2 (@lem1034778 w d' y d h1)). Qed.
Lemma lem1034798 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1034799 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1034798 n m)). Qed.
Lemma lem1034800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034801 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1034800) (@lem1034799 m)). Qed.
Lemma lem1034802 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1034801 m)). Qed.
Lemma lem1034803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034805 : term216 = term216.
Proof. exact (MK_COMB (@lem1034803) (@lem1034802)). Qed.
Lemma lem1034806 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1034805) (@lem1034630 h1)). Qed.
Lemma lem1034820 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1034837 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1034838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1034839 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1034838) (@lem1034837 w x y z)). Qed.
Lemma lem1034840 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1034839 w x y z) (@lem1034820 w x y z)). Qed.
Lemma lem1034849 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1034850 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1034849 w x d y z e) (@lem1034840 w x y z)). Qed.
Lemma lem1034851 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1034852 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1034859 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1034860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1034861 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1034860) (@lem1034859 d e w x y z)). Qed.
Lemma lem1034862 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1034861 d e w x y z) (@lem1034852 d e w x y z)). Qed.
Lemma lem1034863 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1034851 d e w x y z) (@lem1034862 d e w x y z)). Qed.
Lemma lem1034864 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1034850 d e w x y z) (@lem1034863 d e w x y z)). Qed.
Lemma lem1034865 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1034864 d e w x y z)). Qed.
Lemma lem1034866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034867 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1034866) (@lem1034865 d e w x y)). Qed.
Lemma lem1034868 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1034867 d e w x y)). Qed.
Lemma lem1034869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034870 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1034869) (@lem1034868 d e w x)). Qed.
Lemma lem1034871 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1034870 d e w x)). Qed.
Lemma lem1034872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034873 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1034872) (@lem1034871 d e w)). Qed.
Lemma lem1034874 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1034873 d e w)). Qed.
Lemma lem1034875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034876 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1034875) (@lem1034874 d e)). Qed.
Lemma lem1034877 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1034876 d e)). Qed.
Lemma lem1034878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034879 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1034878) (@lem1034877 d)). Qed.
Lemma lem1034880 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1034879 d)). Qed.
Lemma lem1034881 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034883 : term258 = term284.
Proof. exact (MK_COMB (@lem1034881) (@lem1034880)). Qed.
Lemma lem1034884 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1034883) (@lem1034776 h1)). Qed.
Lemma lem1034908 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1034909 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1034908 n m)). Qed.
Lemma lem1034910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034911 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1034910) (@lem1034909 m)). Qed.
Lemma lem1034912 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1034911 m)). Qed.
Lemma lem1034913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034915 : term216 = term216.
Proof. exact (MK_COMB (@lem1034913) (@lem1034912)). Qed.
Lemma lem1034916 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1034915) (@lem1034630 h1)). Qed.
Lemma lem1034930 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1034947 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1034948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1034949 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1034948) (@lem1034947 w x y z)). Qed.
Lemma lem1034950 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1034949 w x y z) (@lem1034930 w x y z)). Qed.
Lemma lem1034959 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1034960 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1034959 w x d y z e) (@lem1034950 w x y z)). Qed.
Lemma lem1034961 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1034962 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1034969 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1034970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1034971 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1034970) (@lem1034969 d e w x y z)). Qed.
Lemma lem1034972 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1034971 d e w x y z) (@lem1034962 d e w x y z)). Qed.
Lemma lem1034973 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1034961 d e w x y z) (@lem1034972 d e w x y z)). Qed.
Lemma lem1034974 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1034960 d e w x y z) (@lem1034973 d e w x y z)). Qed.
Lemma lem1034975 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1034974 d e w x y z)). Qed.
Lemma lem1034976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034977 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1034976) (@lem1034975 d e w x y)). Qed.
Lemma lem1034978 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1034977 d e w x y)). Qed.
Lemma lem1034979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034980 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1034979) (@lem1034978 d e w x)). Qed.
Lemma lem1034981 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1034980 d e w x)). Qed.
Lemma lem1034982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034983 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1034982) (@lem1034981 d e w)). Qed.
Lemma lem1034984 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1034983 d e w)). Qed.
Lemma lem1034985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034986 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1034985) (@lem1034984 d e)). Qed.
Lemma lem1034987 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1034986 d e)). Qed.
Lemma lem1034988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034989 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1034988) (@lem1034987 d)). Qed.
Lemma lem1034990 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1034989 d)). Qed.
Lemma lem1034991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1034993 : term258 = term284.
Proof. exact (MK_COMB (@lem1034991) (@lem1034990)). Qed.
Lemma lem1034994 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1034993) (@lem1034776 h1)). Qed.
Lemma lem1035002 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1035108 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1035115 (_17106 : nat) (h1 : term216) : term285 _17106.
Proof. exact (@lem1034806 h1 _17106). Qed.
Lemma lem1035116 (_17106 : nat) : (term285 _17106) = (term214 _17106).
Proof. exact (eq_refl (term285 _17106)). Qed.
Lemma lem1035117 (_17106 : nat) (h1 : term216) : term214 _17106.
Proof. exact (EQ_MP (@lem1035116 _17106) (@lem1035115 _17106 h1)). Qed.
Lemma lem1035118 (_17106 : nat) (_17107 : nat) (h1 : term216) : term286 _17106 _17107.
Proof. exact (@lem1035117 _17106 h1 _17107). Qed.
Lemma lem1035119 (_17107 : nat) (_17106 : nat) : (term286 _17106 _17107) = ((Nat.add _17106 _17107) = (Nat.add _17107 _17106)).
Proof. exact (eq_refl (term286 _17106 _17107)). Qed.
Lemma lem1035121 (_17108 : nat) (h1 : term107) : term287 _17108.
Proof. exact (@lem1034884 h1 _17108). Qed.
Lemma lem1035122 (_17108 : nat) : (term287 _17108) = (term282 _17108).
Proof. exact (eq_refl (term287 _17108)). Qed.
Lemma lem1035123 (_17108 : nat) (h1 : term107) : term282 _17108.
Proof. exact (EQ_MP (@lem1035122 _17108) (@lem1035121 _17108 h1)). Qed.
Lemma lem1035124 (_17108 : nat) (_17109 : nat) (h1 : term107) : term288 _17108 _17109.
Proof. exact (@lem1035123 _17108 h1 _17109). Qed.
Lemma lem1035125 (_17108 : nat) (_17109 : nat) : (term288 _17108 _17109) = (term280 _17108 _17109).
Proof. exact (eq_refl (term288 _17108 _17109)). Qed.
Lemma lem1035126 (_17108 : nat) (_17109 : nat) (h1 : term107) : term280 _17108 _17109.
Proof. exact (EQ_MP (@lem1035125 _17108 _17109) (@lem1035124 _17108 _17109 h1)). Qed.
Lemma lem1035127 (_17108 : nat) (_17109 : nat) (_17110 : nat) (h1 : term107) : term289 _17108 _17109 _17110.
Proof. exact (@lem1035126 _17108 _17109 h1 _17110). Qed.
Lemma lem1035128 (_17108 : nat) (_17109 : nat) (_17110 : nat) : (term289 _17108 _17109 _17110) = (term278 _17108 _17109 _17110).
Proof. exact (eq_refl (term289 _17108 _17109 _17110)). Qed.
Lemma lem1035129 (_17108 : nat) (_17109 : nat) (_17110 : nat) (h1 : term107) : term278 _17108 _17109 _17110.
Proof. exact (EQ_MP (@lem1035128 _17108 _17109 _17110) (@lem1035127 _17108 _17109 _17110 h1)). Qed.
Lemma lem1035130 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (h1 : term107) : term290 _17108 _17109 _17110 _17111.
Proof. exact (@lem1035129 _17108 _17109 _17110 h1 _17111). Qed.
Lemma lem1035131 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) : (term290 _17108 _17109 _17110 _17111) = (term276 _17108 _17109 _17110 _17111).
Proof. exact (eq_refl (term290 _17108 _17109 _17110 _17111)). Qed.
Lemma lem1035132 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (h1 : term107) : term276 _17108 _17109 _17110 _17111.
Proof. exact (EQ_MP (@lem1035131 _17108 _17109 _17110 _17111) (@lem1035130 _17108 _17109 _17110 _17111 h1)). Qed.
Lemma lem1035133 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (h1 : term107) : term291 _17108 _17109 _17110 _17111 _17112.
Proof. exact (@lem1035132 _17108 _17109 _17110 _17111 h1 _17112). Qed.
Lemma lem1035134 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) : (term291 _17108 _17109 _17110 _17111 _17112) = (term274 _17108 _17109 _17110 _17111 _17112).
Proof. exact (eq_refl (term291 _17108 _17109 _17110 _17111 _17112)). Qed.
Lemma lem1035135 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (h1 : term107) : term274 _17108 _17109 _17110 _17111 _17112.
Proof. exact (EQ_MP (@lem1035134 _17108 _17109 _17110 _17111 _17112) (@lem1035133 _17108 _17109 _17110 _17111 _17112 h1)). Qed.
Lemma lem1035136 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) (h1 : term107) : term292 _17108 _17109 _17110 _17111 _17112 _17113.
Proof. exact (@lem1035135 _17108 _17109 _17110 _17111 _17112 h1 _17113). Qed.
Lemma lem1035137 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term292 _17108 _17109 _17110 _17111 _17112 _17113) = (term272 _17108 _17109 _17110 _17111 _17112 _17113).
Proof. exact (eq_refl (term292 _17108 _17109 _17110 _17111 _17112 _17113)). Qed.
Lemma lem1035138 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) (h1 : term107) : term272 _17108 _17109 _17110 _17111 _17112 _17113.
Proof. exact (EQ_MP (@lem1035137 _17108 _17109 _17110 _17111 _17112 _17113) (@lem1035136 _17108 _17109 _17110 _17111 _17112 _17113 h1)). Qed.
Lemma lem1035145 (_17116 : nat) (h1 : term216) : term285 _17116.
Proof. exact (@lem1034916 h1 _17116). Qed.
Lemma lem1035146 (_17116 : nat) : (term285 _17116) = (term214 _17116).
Proof. exact (eq_refl (term285 _17116)). Qed.
Lemma lem1035147 (_17116 : nat) (h1 : term216) : term214 _17116.
Proof. exact (EQ_MP (@lem1035146 _17116) (@lem1035145 _17116 h1)). Qed.
Lemma lem1035148 (_17116 : nat) (_17117 : nat) (h1 : term216) : term286 _17116 _17117.
Proof. exact (@lem1035147 _17116 h1 _17117). Qed.
Lemma lem1035149 (_17117 : nat) (_17116 : nat) : (term286 _17116 _17117) = ((Nat.add _17116 _17117) = (Nat.add _17117 _17116)).
Proof. exact (eq_refl (term286 _17116 _17117)). Qed.
Lemma lem1035151 (_17118 : nat) (h1 : term107) : term287 _17118.
Proof. exact (@lem1034994 h1 _17118). Qed.
Lemma lem1035152 (_17118 : nat) : (term287 _17118) = (term282 _17118).
Proof. exact (eq_refl (term287 _17118)). Qed.
Lemma lem1035153 (_17118 : nat) (h1 : term107) : term282 _17118.
Proof. exact (EQ_MP (@lem1035152 _17118) (@lem1035151 _17118 h1)). Qed.
Lemma lem1035154 (_17118 : nat) (_17119 : nat) (h1 : term107) : term288 _17118 _17119.
Proof. exact (@lem1035153 _17118 h1 _17119). Qed.
Lemma lem1035155 (_17118 : nat) (_17119 : nat) : (term288 _17118 _17119) = (term280 _17118 _17119).
Proof. exact (eq_refl (term288 _17118 _17119)). Qed.
Lemma lem1035156 (_17118 : nat) (_17119 : nat) (h1 : term107) : term280 _17118 _17119.
Proof. exact (EQ_MP (@lem1035155 _17118 _17119) (@lem1035154 _17118 _17119 h1)). Qed.
Lemma lem1035157 (_17118 : nat) (_17119 : nat) (_17120 : nat) (h1 : term107) : term289 _17118 _17119 _17120.
Proof. exact (@lem1035156 _17118 _17119 h1 _17120). Qed.
Lemma lem1035158 (_17118 : nat) (_17119 : nat) (_17120 : nat) : (term289 _17118 _17119 _17120) = (term278 _17118 _17119 _17120).
Proof. exact (eq_refl (term289 _17118 _17119 _17120)). Qed.
Lemma lem1035159 (_17118 : nat) (_17119 : nat) (_17120 : nat) (h1 : term107) : term278 _17118 _17119 _17120.
Proof. exact (EQ_MP (@lem1035158 _17118 _17119 _17120) (@lem1035157 _17118 _17119 _17120 h1)). Qed.
Lemma lem1035160 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (h1 : term107) : term290 _17118 _17119 _17120 _17121.
Proof. exact (@lem1035159 _17118 _17119 _17120 h1 _17121). Qed.
Lemma lem1035161 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term290 _17118 _17119 _17120 _17121) = (term276 _17118 _17119 _17120 _17121).
Proof. exact (eq_refl (term290 _17118 _17119 _17120 _17121)). Qed.
Lemma lem1035162 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (h1 : term107) : term276 _17118 _17119 _17120 _17121.
Proof. exact (EQ_MP (@lem1035161 _17118 _17119 _17120 _17121) (@lem1035160 _17118 _17119 _17120 _17121 h1)). Qed.
Lemma lem1035163 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (h1 : term107) : term291 _17118 _17119 _17120 _17121 _17122.
Proof. exact (@lem1035162 _17118 _17119 _17120 _17121 h1 _17122). Qed.
Lemma lem1035164 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) : (term291 _17118 _17119 _17120 _17121 _17122) = (term274 _17118 _17119 _17120 _17121 _17122).
Proof. exact (eq_refl (term291 _17118 _17119 _17120 _17121 _17122)). Qed.
Lemma lem1035165 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (h1 : term107) : term274 _17118 _17119 _17120 _17121 _17122.
Proof. exact (EQ_MP (@lem1035164 _17118 _17119 _17120 _17121 _17122) (@lem1035163 _17118 _17119 _17120 _17121 _17122 h1)). Qed.
Lemma lem1035166 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (h1 : term107) : term292 _17118 _17119 _17120 _17121 _17122 _17123.
Proof. exact (@lem1035165 _17118 _17119 _17120 _17121 _17122 h1 _17123). Qed.
Lemma lem1035167 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) : (term292 _17118 _17119 _17120 _17121 _17122 _17123) = (term272 _17118 _17119 _17120 _17121 _17122 _17123).
Proof. exact (eq_refl (term292 _17118 _17119 _17120 _17121 _17122 _17123)). Qed.
Lemma lem1035168 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (h1 : term107) : term272 _17118 _17119 _17120 _17121 _17122 _17123.
Proof. exact (EQ_MP (@lem1035167 _17118 _17119 _17120 _17121 _17122 _17123) (@lem1035166 _17118 _17119 _17120 _17121 _17122 _17123 h1)). Qed.
Lemma lem1035199 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) (h1 : term107) : term265 _17108 _17109 _17110 _17111 _17112 _17113.
Proof. exact (proj2 (@lem1035138 _17108 _17109 _17110 _17111 _17112 _17113 h1)). Qed.
Lemma lem1035204 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (h1 : term107) : term267 _17118 _17119 _17120 _17121 _17122 _17123.
Proof. exact (proj1 (@lem1035168 _17118 _17119 _17120 _17121 _17122 _17123 h1)). Qed.
Lemma lem1035206 (_17118 : nat) (_17119 : nat) (_17123 : nat) (_17122 : nat) (_17120 : nat) (_17121 : nat) (h1 : term107) : term293 _17118 _17119 _17123 _17122 _17120 _17121.
Proof. exact (proj1 (@lem1035204 _17118 _17119 _17120 _17121 _17122 _17123 h1)). Qed.
Lemma lem1035220 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term294 y d.
Proof. exact (proj2 (@lem1034779 w d' y d h1)). Qed.
Lemma lem1035239 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term265 _17108 _17109 _17110 _17111 _17112 _17113) = (term295 _17108 _17109 _17110 _17111 _17112 _17113).
Proof. exact (@lem1033471 (term296 _17110 _17111 _17108) (term296 _17112 _17113 _17109) (term235 _17110 _17111 _17112 _17113)). Qed.
Lemma lem1035240 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) (h1 : term107) : term295 _17108 _17109 _17110 _17111 _17112 _17113.
Proof. exact (EQ_MP (@lem1035239 _17108 _17109 _17110 _17111 _17112 _17113) (@lem1035199 _17108 _17109 _17110 _17111 _17112 _17113 h1)). Qed.
Lemma lem1035278 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term297 d w d' y.
Proof. exact (proj1 (@lem1034778 w d' y d h1)). Qed.
Lemma lem1035280 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1035315 (_17118 : nat) (_17119 : nat) (_17123 : nat) (_17122 : nat) (_17120 : nat) (_17121 : nat) : (term293 _17118 _17119 _17123 _17122 _17120 _17121) = (term298 _17118 _17119 _17123 _17122 _17120 _17121).
Proof. exact (@lem1033471 (term296 _17120 _17121 _17118) (term296 _17122 _17123 _17119) (term268 _17123 _17122 _17120 _17121)). Qed.
Lemma lem1035316 (_17118 : nat) (_17119 : nat) (_17123 : nat) (_17122 : nat) (_17120 : nat) (_17121 : nat) (h1 : term107) : term298 _17118 _17119 _17123 _17122 _17120 _17121.
Proof. exact (EQ_MP (@lem1035315 _17118 _17119 _17123 _17122 _17120 _17121) (@lem1035206 _17118 _17119 _17123 _17122 _17120 _17121 h1)). Qed.
Lemma lem1035338 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term297 d w d' y.
Proof. exact (proj1 (@lem1034778 w d' y d h1)). Qed.
Lemma lem1035340 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1035424 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1035426 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1035427 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1035426 (Nat.add w d')). Qed.
Lemma lem1035428 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1035427 w d'). Qed.
Lemma lem1035430 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035431 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1035430 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1035432 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1035431 w d') (@lem1035428 w d')). Qed.
Lemma lem1035434 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1035435 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1035434 (Nat.add y d)). Qed.
Lemma lem1035436 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1035435 y d). Qed.
Lemma lem1035438 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035439 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1035438 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1035440 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1035439 y d) (@lem1035436 y d)). Qed.
Lemma lem1035442 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (proj1 (@lem1034777 w d' y d h1)). Qed.
Lemma lem1035443 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term303 d w d' y.
Proof. exact (fun h0 : term297 d w d' y => @lem1035442 w d' y d h1). Qed.
Lemma lem1035445 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035446 (d : nat) (w : nat) (d' : nat) (y : nat) : (term303 d w d' y) = ((term149 w d' y d) = (term150 d w d' y)).
Proof. exact (@lem1035445 ((term149 w d' y d) = (term150 d w d' y))). Qed.
Lemma lem1035447 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (EQ_MP (@lem1035446 d w d' y) (@lem1035443 w d' y d h1)). Qed.
Lemma lem1035449 (_17107 : nat) (_17106 : nat) (h1 : term216) : (Nat.add _17106 _17107) = (Nat.add _17107 _17106).
Proof. exact (EQ_MP (@lem1035119 _17107 _17106) (@lem1035118 _17106 _17107 h1)). Qed.
Lemma lem1035450 (d' : nat) (d : nat) (w : nat) (y : nat) (h1 : term216) : (term149 w d' y d) = (term54 d' d w y).
Proof. exact (@lem1035449 (term50 w d' y d) (Nat.mul w y) h1). Qed.
Lemma lem1035451 (d' : nat) (d : nat) (w : nat) (y : nat) (h1 : term216) : term304 d' d w y.
Proof. exact (fun h0 : term305 d' d w y => @lem1035450 d' d w y h1). Qed.
Lemma lem1035453 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035454 (d' : nat) (d : nat) (w : nat) (y : nat) : (term304 d' d w y) = ((term149 w d' y d) = (term54 d' d w y)).
Proof. exact (@lem1035453 ((term149 w d' y d) = (term54 d' d w y))). Qed.
Lemma lem1035455 (d' : nat) (d : nat) (w : nat) (y : nat) (h1 : term216) : (term149 w d' y d) = (term54 d' d w y).
Proof. exact (EQ_MP (@lem1035454 d' d w y) (@lem1035451 d' d w y h1)). Qed.
Lemma lem1035473 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1035474 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1035473 (y = z) (term260 x z)). Qed.
Lemma lem1035484 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1035485 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1035484 x y) (@lem1035474 y x z)). Qed.
Lemma lem1035489 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035490 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1035489 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1035512 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1035485 y x z) (@lem1035490 y x z)). Qed.
Lemma lem1035513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1035514 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1035513) (@lem1035512 y x z)). Qed.
Lemma lem1035536 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1035537 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1035514 y x z) (@lem1035536 y x z)). Qed.
Lemma lem1035539 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1035540 (x : Prop) : (x = x) = True.
Proof. exact (@lem1035539 Prop x). Qed.
Lemma lem1035541 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1035540 (term310 y x z)). Qed.
Lemma lem1035542 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1035537 y x z) (@lem1035541 y x z)). Qed.
Lemma lem1035543 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1035542 y x z)). Qed.
Lemma lem1035544 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1035543 y x z) (@lem0)). Qed.
Lemma lem1035545 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1035544 y x z) (@lem1035424 x y z)). Qed.
Lemma lem1035547 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1035548 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1035547 (term315 y x z) (y = z)). Qed.
Lemma lem1035550 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1035551 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1035550 (term260 x y) (term260 x z)). Qed.
Lemma lem1035553 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1035554 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1035553 (x = y)). Qed.
Lemma lem1035555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1035556 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1035555) (@lem1035554 x y)). Qed.
Lemma lem1035558 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1035559 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1035558 (x = z)). Qed.
Lemma lem1035560 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1035556 x y) (@lem1035559 x z)). Qed.
Lemma lem1035561 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1035551 y x z) (@lem1035560 y x z)). Qed.
Lemma lem1035562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1035563 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1035562) (@lem1035561 y x z)). Qed.
Lemma lem1035564 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1035565 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1035563 y x z) (@lem1035564 y z)). Qed.
Lemma lem1035566 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1035548 x y z) (@lem1035565 x y z)). Qed.
Lemma lem1035568 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term328 d' d w y.
Proof. exact (conj (@lem1035447 w d' y d h2) (@lem1035455 d' d w y h1)). Qed.
Lemma lem1035570 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1035566 x y z) (@lem1035545 y x z)). Qed.
Lemma lem1035571 (d' : nat) (d : nat) (w : nat) (y : nat) : term329 d' d w y.
Proof. exact (@lem1035570 (term149 w d' y d) (term150 d w d' y) (term54 d' d w y)). Qed.
Lemma lem1035574 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : (term150 d w d' y) = (term54 d' d w y).
Proof. exact (@lem1035571 d' d w y (@lem1035568 w d' y d h1 h2)). Qed.
Lemma lem1035575 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term330 d' d w y.
Proof. exact (fun h0 : term331 d' d w y => @lem1035574 w d' y d h1 h2). Qed.
Lemma lem1035577 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035578 (d' : nat) (d : nat) (w : nat) (y : nat) : (term330 d' d w y) = ((term150 d w d' y) = (term54 d' d w y)).
Proof. exact (@lem1035577 ((term150 d w d' y) = (term54 d' d w y))). Qed.
Lemma lem1035579 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : (term150 d w d' y) = (term54 d' d w y).
Proof. exact (EQ_MP (@lem1035578 d' d w y) (@lem1035575 w d' y d h1 h2)). Qed.
Lemma lem1035581 (_17107 : nat) (_17106 : nat) (h1 : term216) : (Nat.add _17106 _17107) = (Nat.add _17107 _17106).
Proof. exact (EQ_MP (@lem1035119 _17107 _17106) (@lem1035118 _17106 _17107 h1)). Qed.
Lemma lem1035582 (d' : nat) (w : nat) (y : nat) (d : nat) (h1 : term216) : (term150 d w d' y) = (term58 d' w y d).
Proof. exact (@lem1035581 (term39 w d' y) (term46 w y d) h1). Qed.
Lemma lem1035583 (d' : nat) (w : nat) (y : nat) (d : nat) (h1 : term216) : term332 d' w y d.
Proof. exact (fun h0 : term333 d' w y d => @lem1035582 d' w y d h1). Qed.
Lemma lem1035585 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035586 (d' : nat) (w : nat) (y : nat) (d : nat) : (term332 d' w y d) = ((term150 d w d' y) = (term58 d' w y d)).
Proof. exact (@lem1035585 ((term150 d w d' y) = (term58 d' w y d))). Qed.
Lemma lem1035587 (d' : nat) (w : nat) (y : nat) (d : nat) (h1 : term216) : (term150 d w d' y) = (term58 d' w y d).
Proof. exact (EQ_MP (@lem1035586 d' w y d) (@lem1035583 d' w y d h1)). Qed.
Lemma lem1035588 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term334 d' w y d.
Proof. exact (conj (@lem1035579 w d' y d h1 h2) (@lem1035587 d' w y d h1)). Qed.
Lemma lem1035590 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1035566 x y z) (@lem1035545 y x z)). Qed.
Lemma lem1035591 (d' : nat) (w : nat) (y : nat) (d : nat) : term335 d' w y d.
Proof. exact (@lem1035590 (term150 d w d' y) (term54 d' d w y) (term58 d' w y d)). Qed.
Lemma lem1035594 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : (term54 d' d w y) = (term58 d' w y d).
Proof. exact (@lem1035591 d' w y d (@lem1035588 w d' y d h1 h2)). Qed.
Lemma lem1035595 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term336 d' w y d.
Proof. exact (fun h0 : term337 d' w y d => @lem1035594 w d' y d h1 h2). Qed.
Lemma lem1035597 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035598 (d' : nat) (w : nat) (y : nat) (d : nat) : (term336 d' w y d) = ((term54 d' d w y) = (term58 d' w y d)).
Proof. exact (@lem1035597 ((term54 d' d w y) = (term58 d' w y d))). Qed.
Lemma lem1035599 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : (term54 d' d w y) = (term58 d' w y d).
Proof. exact (EQ_MP (@lem1035598 d' w y d) (@lem1035595 w d' y d h1 h2)). Qed.
Lemma lem1035601 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1035602 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1035601 (Nat.add w d')). Qed.
Lemma lem1035603 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1035602 w d'). Qed.
Lemma lem1035605 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1035606 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1035605 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1035607 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1035606 w d') (@lem1035603 w d')). Qed.
Lemma lem1035609 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term294 w d'.
Proof. exact (proj1 (@lem1034779 w d' y d h1)). Qed.
Lemma lem1035610 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term338 w d'.
Proof. exact (fun h0 : w = (Nat.add w d') => @lem1035609 w d' y d h1). Qed.
Lemma lem1035612 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1035613 (w : nat) (d' : nat) : (term338 w d') = (term294 w d').
Proof. exact (@lem1035612 (w = (Nat.add w d'))). Qed.
Lemma lem1035614 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term294 w d'.
Proof. exact (EQ_MP (@lem1035613 w d') (@lem1035610 w d' y d h1)). Qed.
Lemma lem1035616 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1035617 (z : nat) (x : nat) (y : nat) : (term299 x y z) = (term340 z x y).
Proof. exact (@lem1035616 (term306 x y z) (term260 x y)). Qed.
Lemma lem1035619 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1035620 (x : nat) (y : nat) (z : nat) : (term341 x y z) = (term342 x y z).
Proof. exact (@lem1035619 (term260 x z) (y = z)). Qed.
Lemma lem1035622 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1035623 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1035622 (x = z)). Qed.
Lemma lem1035624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1035625 (x : nat) (z : nat) : (term322 x z) = (term323 x z).
Proof. exact (MK_COMB (@lem1035624) (@lem1035623 x z)). Qed.
Lemma lem1035626 (y : nat) (z : nat) : (term260 y z) = (term260 y z).
Proof. exact (eq_refl (term260 y z)). Qed.
Lemma lem1035627 (x : nat) (y : nat) (z : nat) : (term342 x y z) = (term343 x y z).
Proof. exact (MK_COMB (@lem1035625 x z) (@lem1035626 y z)). Qed.
Lemma lem1035628 (x : nat) (y : nat) (z : nat) : (term341 x y z) = (term343 x y z).
Proof. exact (TRANS (@lem1035620 x y z) (@lem1035627 x y z)). Qed.
Lemma lem1035629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1035630 (x : nat) (y : nat) (z : nat) : (term344 x y z) = (term345 x y z).
Proof. exact (MK_COMB (@lem1035629) (@lem1035628 x y z)). Qed.
Lemma lem1035631 (x : nat) (y : nat) : (term260 x y) = (term260 x y).
Proof. exact (eq_refl (term260 x y)). Qed.
Lemma lem1035632 (z : nat) (x : nat) (y : nat) : (term340 z x y) = (term346 z x y).
Proof. exact (MK_COMB (@lem1035630 x y z) (@lem1035631 x y)). Qed.
Lemma lem1035633 (z : nat) (x : nat) (y : nat) : (term299 x y z) = (term346 z x y).
Proof. exact (TRANS (@lem1035617 z x y) (@lem1035632 z x y)). Qed.
Lemma lem1035635 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term347 w d'.
Proof. exact (conj (@lem1035607 w d') (@lem1035614 w d' y d h1)). Qed.
Lemma lem1035637 (z : nat) (x : nat) (y : nat) : term346 z x y.
Proof. exact (EQ_MP (@lem1035633 z x y) (@lem1035424 x y z)). Qed.
Lemma lem1035638 (d' : nat) (w : nat) : term348 d' w.
Proof. exact (@lem1035637 (Nat.add w d') (Nat.add w d') w). Qed.
Lemma lem1035641 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term349 d' w.
Proof. exact (@lem1035638 d' w (@lem1035635 w d' y d h1)). Qed.
Lemma lem1035642 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term350 d' w.
Proof. exact (fun h0 : (Nat.add w d') = w => @lem1035641 w d' y d h1). Qed.
Lemma lem1035644 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1035645 (d' : nat) (w : nat) : (term350 d' w) = (term349 d' w).
Proof. exact (@lem1035644 ((Nat.add w d') = w)). Qed.
Lemma lem1035646 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term349 d' w.
Proof. exact (EQ_MP (@lem1035645 d' w) (@lem1035642 w d' y d h1)). Qed.
Lemma lem1035676 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035677 (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term235 _17110 _17111 _17112 _17113) = (term351 _17110 _17111 _17112 _17113).
Proof. exact (@lem1035676 (_17110 = _17111) (term352 _17110 _17113 _17111 _17112) (_17112 = _17113)). Qed.
Lemma lem1035693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1035694 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term353 _17110 _17111 _17112 _17113) = (term354 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035693 (_17112 = _17113) (term352 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035704 (_17110 : nat) (_17111 : nat) : (term62 _17110 _17111) = (term62 _17110 _17111).
Proof. exact (eq_refl (term62 _17110 _17111)). Qed.
Lemma lem1035705 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term351 _17110 _17111 _17112 _17113) = (term355 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035704 _17110 _17111) (@lem1035694 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035716 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term235 _17110 _17111 _17112 _17113) = (term355 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035677 _17110 _17111 _17112 _17113) (@lem1035705 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035717 (_17112 : nat) (_17113 : nat) (_17109 : nat) : (term356 _17112 _17113 _17109) = (term356 _17112 _17113 _17109).
Proof. exact (eq_refl (term356 _17112 _17113 _17109)). Qed.
Lemma lem1035718 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term357 _17109 _17110 _17111 _17112 _17113) = (term358 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035717 _17112 _17113 _17109) (@lem1035716 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035722 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035723 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term358 _17109 _17110 _17113 _17111 _17112) = (term359 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035722 (_17110 = _17111) (term296 _17112 _17113 _17109) (term354 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035739 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035740 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term360 _17109 _17110 _17113 _17111 _17112) = (term361 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035739 (_17112 = _17113) (term296 _17112 _17113 _17109) (term352 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035762 (_17110 : nat) (_17111 : nat) : (term62 _17110 _17111) = (term62 _17110 _17111).
Proof. exact (eq_refl (term62 _17110 _17111)). Qed.
Lemma lem1035763 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term359 _17109 _17110 _17113 _17111 _17112) = (term362 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035762 _17110 _17111) (@lem1035740 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035774 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term358 _17109 _17110 _17113 _17111 _17112) = (term362 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035723 _17109 _17110 _17113 _17111 _17112) (@lem1035763 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035775 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term357 _17109 _17110 _17111 _17112 _17113) = (term362 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035718 _17109 _17110 _17113 _17111 _17112) (@lem1035774 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035776 (_17110 : nat) (_17111 : nat) (_17108 : nat) : (term356 _17110 _17111 _17108) = (term356 _17110 _17111 _17108).
Proof. exact (eq_refl (term356 _17110 _17111 _17108)). Qed.
Lemma lem1035777 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term363 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035776 _17110 _17111 _17108) (@lem1035775 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035781 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035782 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term363 _17108 _17109 _17110 _17113 _17111 _17112) = (term364 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035781 (_17110 = _17111) (term296 _17110 _17111 _17108) (term361 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035798 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035799 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term365 _17108 _17109 _17110 _17113 _17111 _17112) = (term366 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035798 (_17112 = _17113) (term296 _17110 _17111 _17108) (term367 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035833 (_17110 : nat) (_17111 : nat) : (term62 _17110 _17111) = (term62 _17110 _17111).
Proof. exact (eq_refl (term62 _17110 _17111)). Qed.
Lemma lem1035834 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term364 _17108 _17109 _17110 _17113 _17111 _17112) = (term368 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035833 _17110 _17111) (@lem1035799 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035845 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term363 _17108 _17109 _17110 _17113 _17111 _17112) = (term368 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035782 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1035834 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035846 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term368 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035777 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1035845 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1035848 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term369 _17108 _17109 _17110 _17111 _17112 _17113) = (term370 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035847) (@lem1035846 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1035889 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term371 _17113 _17112 _17110 _17111) = (term372 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035888 (_17110 = _17111) (term352 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035899 (_17112 : nat) (_17113 : nat) (_17109 : nat) : (term356 _17112 _17113 _17109) = (term356 _17112 _17113 _17109).
Proof. exact (eq_refl (term356 _17112 _17113 _17109)). Qed.
Lemma lem1035900 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term373 _17109 _17113 _17112 _17110 _17111) = (term374 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035899 _17112 _17113 _17109) (@lem1035889 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035904 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035905 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term374 _17109 _17110 _17113 _17111 _17112) = (term375 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035904 (_17110 = _17111) (term296 _17112 _17113 _17109) (term352 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035927 (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term373 _17109 _17113 _17112 _17110 _17111) = (term375 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035900 _17109 _17110 _17113 _17111 _17112) (@lem1035905 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035928 (_17110 : nat) (_17111 : nat) (_17108 : nat) : (term356 _17110 _17111 _17108) = (term356 _17110 _17111 _17108).
Proof. exact (eq_refl (term356 _17110 _17111 _17108)). Qed.
Lemma lem1035929 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term376 _17108 _17109 _17113 _17112 _17110 _17111) = (term377 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035928 _17110 _17111 _17108) (@lem1035927 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035933 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035934 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term377 _17108 _17109 _17110 _17113 _17111 _17112) = (term378 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035933 (_17110 = _17111) (term296 _17110 _17111 _17108) (term367 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035968 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term376 _17108 _17109 _17113 _17112 _17110 _17111) = (term378 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035929 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1035934 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035969 (_17112 : nat) (_17113 : nat) : (term62 _17112 _17113) = (term62 _17112 _17113).
Proof. exact (eq_refl (term62 _17112 _17113)). Qed.
Lemma lem1035970 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term379 _17108 _17109 _17113 _17112 _17110 _17111) = (term380 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1035969 _17112 _17113) (@lem1035968 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1035974 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1035975 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term380 _17108 _17109 _17110 _17113 _17111 _17112) = (term368 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (@lem1035974 (_17110 = _17111) (_17112 = _17113) (term381 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036021 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term379 _17108 _17109 _17113 _17112 _17110 _17111) = (term368 _17108 _17109 _17110 _17113 _17111 _17112).
Proof. exact (TRANS (@lem1035970 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1035975 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036022 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : ((term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term379 _17108 _17109 _17113 _17112 _17110 _17111)) = ((term368 _17108 _17109 _17110 _17113 _17111 _17112) = (term368 _17108 _17109 _17110 _17113 _17111 _17112)).
Proof. exact (MK_COMB (@lem1035848 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1036021 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036024 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1036025 (x : Prop) : (x = x) = True.
Proof. exact (@lem1036024 Prop x). Qed.
Lemma lem1036026 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : ((term368 _17108 _17109 _17110 _17113 _17111 _17112) = (term368 _17108 _17109 _17110 _17113 _17111 _17112)) = True.
Proof. exact (@lem1036025 (term368 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036027 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : ((term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term379 _17108 _17109 _17113 _17112 _17110 _17111)) = True.
Proof. exact (TRANS (@lem1036022 _17108 _17109 _17110 _17113 _17111 _17112) (@lem1036026 _17108 _17109 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036028 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : True = ((term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term379 _17108 _17109 _17113 _17112 _17110 _17111)).
Proof. exact (SYM (@lem1036027 _17108 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036029 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term295 _17108 _17109 _17110 _17111 _17112 _17113) = (term379 _17108 _17109 _17113 _17112 _17110 _17111).
Proof. exact (EQ_MP (@lem1036028 _17108 _17109 _17113 _17112 _17110 _17111) (@lem0)). Qed.
Lemma lem1036030 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) (h1 : term107) : term379 _17108 _17109 _17113 _17112 _17110 _17111.
Proof. exact (EQ_MP (@lem1036029 _17108 _17109 _17113 _17112 _17110 _17111) (@lem1035240 _17108 _17109 _17110 _17111 _17112 _17113 h1)). Qed.
Lemma lem1036032 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1036033 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term379 _17108 _17109 _17113 _17112 _17110 _17111) = (term382 _17108 _17109 _17110 _17111 _17112 _17113).
Proof. exact (@lem1036032 (term376 _17108 _17109 _17113 _17112 _17110 _17111) (_17112 = _17113)). Qed.
Lemma lem1036035 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036036 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term383 _17108 _17109 _17113 _17112 _17110 _17111) = (term384 _17108 _17109 _17113 _17112 _17110 _17111).
Proof. exact (@lem1036035 (term296 _17110 _17111 _17108) (term373 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036038 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036039 (_17110 : nat) (_17111 : nat) (_17108 : nat) : (term385 _17110 _17111 _17108) = (_17110 = (Nat.add _17111 _17108)).
Proof. exact (@lem1036038 (_17110 = (Nat.add _17111 _17108))). Qed.
Lemma lem1036040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036041 (_17110 : nat) (_17111 : nat) (_17108 : nat) : (term386 _17110 _17111 _17108) = (term387 _17110 _17111 _17108).
Proof. exact (MK_COMB (@lem1036040) (@lem1036039 _17110 _17111 _17108)). Qed.
Lemma lem1036043 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036044 (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term388 _17109 _17113 _17112 _17110 _17111) = (term389 _17109 _17113 _17112 _17110 _17111).
Proof. exact (@lem1036043 (term296 _17112 _17113 _17109) (term371 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036046 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036047 (_17112 : nat) (_17113 : nat) (_17109 : nat) : (term385 _17112 _17113 _17109) = (_17112 = (Nat.add _17113 _17109)).
Proof. exact (@lem1036046 (_17112 = (Nat.add _17113 _17109))). Qed.
Lemma lem1036048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036049 (_17112 : nat) (_17113 : nat) (_17109 : nat) : (term386 _17112 _17113 _17109) = (term387 _17112 _17113 _17109).
Proof. exact (MK_COMB (@lem1036048) (@lem1036047 _17112 _17113 _17109)). Qed.
Lemma lem1036051 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036052 (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term390 _17113 _17112 _17110 _17111) = (term391 _17113 _17112 _17110 _17111).
Proof. exact (@lem1036051 (term352 _17110 _17113 _17111 _17112) (_17110 = _17111)). Qed.
Lemma lem1036054 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036055 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term392 _17110 _17113 _17111 _17112) = ((term53 _17110 _17112 _17111 _17113) = (term53 _17110 _17113 _17111 _17112)).
Proof. exact (@lem1036054 ((term53 _17110 _17112 _17111 _17113) = (term53 _17110 _17113 _17111 _17112))). Qed.
Lemma lem1036056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036057 (_17110 : nat) (_17113 : nat) (_17111 : nat) (_17112 : nat) : (term393 _17110 _17113 _17111 _17112) = (term394 _17110 _17113 _17111 _17112).
Proof. exact (MK_COMB (@lem1036056) (@lem1036055 _17110 _17113 _17111 _17112)). Qed.
Lemma lem1036058 (_17110 : nat) (_17111 : nat) : (term260 _17110 _17111) = (term260 _17110 _17111).
Proof. exact (eq_refl (term260 _17110 _17111)). Qed.
Lemma lem1036059 (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term391 _17113 _17112 _17110 _17111) = (term395 _17113 _17112 _17110 _17111).
Proof. exact (MK_COMB (@lem1036057 _17110 _17113 _17111 _17112) (@lem1036058 _17110 _17111)). Qed.
Lemma lem1036060 (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term390 _17113 _17112 _17110 _17111) = (term395 _17113 _17112 _17110 _17111).
Proof. exact (TRANS (@lem1036052 _17113 _17112 _17110 _17111) (@lem1036059 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036061 (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term389 _17109 _17113 _17112 _17110 _17111) = (term396 _17109 _17113 _17112 _17110 _17111).
Proof. exact (MK_COMB (@lem1036049 _17112 _17113 _17109) (@lem1036060 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036062 (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term388 _17109 _17113 _17112 _17110 _17111) = (term396 _17109 _17113 _17112 _17110 _17111).
Proof. exact (TRANS (@lem1036044 _17109 _17113 _17112 _17110 _17111) (@lem1036061 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036063 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term384 _17108 _17109 _17113 _17112 _17110 _17111) = (term397 _17108 _17109 _17113 _17112 _17110 _17111).
Proof. exact (MK_COMB (@lem1036041 _17110 _17111 _17108) (@lem1036062 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036064 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term383 _17108 _17109 _17113 _17112 _17110 _17111) = (term397 _17108 _17109 _17113 _17112 _17110 _17111).
Proof. exact (TRANS (@lem1036036 _17108 _17109 _17113 _17112 _17110 _17111) (@lem1036063 _17108 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1036066 (_17108 : nat) (_17109 : nat) (_17113 : nat) (_17112 : nat) (_17110 : nat) (_17111 : nat) : (term398 _17108 _17109 _17113 _17112 _17110 _17111) = (term399 _17108 _17109 _17113 _17112 _17110 _17111).
Proof. exact (MK_COMB (@lem1036065) (@lem1036064 _17108 _17109 _17113 _17112 _17110 _17111)). Qed.
Lemma lem1036067 (_17112 : nat) (_17113 : nat) : (_17112 = _17113) = (_17112 = _17113).
Proof. exact (eq_refl (_17112 = _17113)). Qed.
Lemma lem1036068 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term382 _17108 _17109 _17110 _17111 _17112 _17113) = (term400 _17108 _17109 _17110 _17111 _17112 _17113).
Proof. exact (MK_COMB (@lem1036066 _17108 _17109 _17113 _17112 _17110 _17111) (@lem1036067 _17112 _17113)). Qed.
Lemma lem1036069 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) : (term379 _17108 _17109 _17113 _17112 _17110 _17111) = (term400 _17108 _17109 _17110 _17111 _17112 _17113).
Proof. exact (TRANS (@lem1036033 _17108 _17109 _17110 _17111 _17112 _17113) (@lem1036068 _17108 _17109 _17110 _17111 _17112 _17113)). Qed.
Lemma lem1036071 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term401 y d d' w.
Proof. exact (conj (@lem1035599 w d' y d h1 h2) (@lem1035646 w d' y d h2)). Qed.
Lemma lem1036072 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term402 y d d' w.
Proof. exact (conj (@lem1035440 y d) (@lem1036071 w d' y d h1 h2)). Qed.
Lemma lem1036073 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term226 w d' y d) : term403 y d d' w.
Proof. exact (conj (@lem1035432 w d') (@lem1036072 w d' y d h1 h2)). Qed.
Lemma lem1036075 (_17108 : nat) (_17109 : nat) (_17110 : nat) (_17111 : nat) (_17112 : nat) (_17113 : nat) (h1 : term107) : term400 _17108 _17109 _17110 _17111 _17112 _17113.
Proof. exact (EQ_MP (@lem1036069 _17108 _17109 _17110 _17111 _17112 _17113) (@lem1036030 _17108 _17109 _17113 _17112 _17110 _17111 h1)). Qed.
Lemma lem1036076 (d' : nat) (w : nat) (d : nat) (y : nat) (h1 : term107) : term404 d' w d y.
Proof. exact (@lem1036075 d' d (Nat.add w d') w (Nat.add y d) y h1). Qed.
Lemma lem1036079 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : (Nat.add y d) = y.
Proof. exact (@lem1036076 d' w d y h1 (@lem1036073 w d' y d h2 h3)). Qed.
Lemma lem1036080 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : term405 d y.
Proof. exact (fun h0 : term349 d y => @lem1036079 w d' y d h1 h2 h3). Qed.
Lemma lem1036082 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036083 (d : nat) (y : nat) : (term405 d y) = ((Nat.add y d) = y).
Proof. exact (@lem1036082 ((Nat.add y d) = y)). Qed.
Lemma lem1036084 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : (Nat.add y d) = y.
Proof. exact (EQ_MP (@lem1036083 d y) (@lem1036080 w d' y d h1 h2 h3)). Qed.
Lemma lem1036086 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036087 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1036086 (Nat.add y d)). Qed.
Lemma lem1036088 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1036087 y d). Qed.
Lemma lem1036090 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036091 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1036090 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1036092 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1036091 y d) (@lem1036088 y d)). Qed.
Lemma lem1036093 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : term406 y d.
Proof. exact (conj (@lem1036084 w d' y d h1 h2 h3) (@lem1036092 y d)). Qed.
Lemma lem1036095 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1035566 x y z) (@lem1035545 y x z)). Qed.
Lemma lem1036096 (y : nat) (d : nat) : term407 y d.
Proof. exact (@lem1036095 (Nat.add y d) y (Nat.add y d)). Qed.
Lemma lem1036099 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : y = (Nat.add y d).
Proof. exact (@lem1036096 y d (@lem1036093 w d' y d h1 h2 h3)). Qed.
Lemma lem1036100 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : term408 y d.
Proof. exact (fun h0 : term294 y d => @lem1036099 w d' y d h1 h2 h3). Qed.
Lemma lem1036102 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036103 (y : nat) (d : nat) : (term408 y d) = (y = (Nat.add y d)).
Proof. exact (@lem1036102 (y = (Nat.add y d))). Qed.
Lemma lem1036104 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : y = (Nat.add y d).
Proof. exact (EQ_MP (@lem1036103 y d) (@lem1036100 w d' y d h1 h2 h3)). Qed.
Lemma lem1036107 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1036109 (y : nat) (d : nat) : (term294 y d) = (term409 y d).
Proof. exact (@lem1036107 (y = (Nat.add y d))). Qed.
Lemma lem1036112 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term226 w d' y d) : term409 y d.
Proof. exact (EQ_MP (@lem1036109 y d) (@lem1035220 w d' y d h1)). Qed.
Lemma lem1036115 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : False.
Proof. exact (@lem1036112 w d' y d h3 (@lem1036104 w d' y d h1 h2 h3)). Qed.
Lemma lem1036116 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : term410.
Proof. exact (fun h0 : ~ False => @lem1036115 w d' y d h1 h2 h3). Qed.
Lemma lem1036118 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036119 : term410 = False.
Proof. exact (@lem1036118 False). Qed.
Lemma lem1036120 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : False.
Proof. exact (EQ_MP (@lem1036119) (@lem1036116 w d' y d h1 h2 h3)). Qed.
Lemma lem1036152 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1036154 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036155 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1036154 (Nat.add w d')). Qed.
Lemma lem1036156 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1036155 w d'). Qed.
Lemma lem1036158 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036159 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1036158 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1036160 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1036159 w d') (@lem1036156 w d')). Qed.
Lemma lem1036162 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036163 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1036162 (Nat.add y d)). Qed.
Lemma lem1036164 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1036163 y d). Qed.
Lemma lem1036166 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036167 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1036166 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1036168 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1036167 y d) (@lem1036164 y d)). Qed.
Lemma lem1036170 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1036171 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term408 w d'.
Proof. exact (fun h0 : term294 w d' => @lem1036170 w d' h1). Qed.
Lemma lem1036173 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036174 (w : nat) (d' : nat) : (term408 w d') = (w = (Nat.add w d')).
Proof. exact (@lem1036173 (w = (Nat.add w d'))). Qed.
Lemma lem1036175 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (EQ_MP (@lem1036174 w d') (@lem1036171 w d' h1)). Qed.
Lemma lem1036177 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036178 (w : nat) : w = w.
Proof. exact (@lem1036177 w). Qed.
Lemma lem1036179 (w : nat) : term411 w.
Proof. exact (fun h0 : term412 w => @lem1036178 w). Qed.
Lemma lem1036181 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036182 (w : nat) : (term411 w) = (w = w).
Proof. exact (@lem1036181 (w = w)). Qed.
Lemma lem1036183 (w : nat) : w = w.
Proof. exact (EQ_MP (@lem1036182 w) (@lem1036179 w)). Qed.
Lemma lem1036201 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036202 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1036201 (y = z) (term260 x z)). Qed.
Lemma lem1036212 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1036213 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1036212 x y) (@lem1036202 y x z)). Qed.
Lemma lem1036217 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036218 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1036217 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1036240 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1036213 y x z) (@lem1036218 y x z)). Qed.
Lemma lem1036241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1036242 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1036241) (@lem1036240 y x z)). Qed.
Lemma lem1036264 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1036265 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1036242 y x z) (@lem1036264 y x z)). Qed.
Lemma lem1036267 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1036268 (x : Prop) : (x = x) = True.
Proof. exact (@lem1036267 Prop x). Qed.
Lemma lem1036269 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1036268 (term310 y x z)). Qed.
Lemma lem1036270 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1036265 y x z) (@lem1036269 y x z)). Qed.
Lemma lem1036271 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1036270 y x z)). Qed.
Lemma lem1036272 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1036271 y x z) (@lem0)). Qed.
Lemma lem1036273 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1036272 y x z) (@lem1036152 x y z)). Qed.
Lemma lem1036275 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1036276 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1036275 (term315 y x z) (y = z)). Qed.
Lemma lem1036278 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036279 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1036278 (term260 x y) (term260 x z)). Qed.
Lemma lem1036281 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036282 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1036281 (x = y)). Qed.
Lemma lem1036283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036284 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1036283) (@lem1036282 x y)). Qed.
Lemma lem1036286 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036287 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1036286 (x = z)). Qed.
Lemma lem1036288 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1036284 x y) (@lem1036287 x z)). Qed.
Lemma lem1036289 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1036279 y x z) (@lem1036288 y x z)). Qed.
Lemma lem1036290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1036291 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1036290) (@lem1036289 y x z)). Qed.
Lemma lem1036292 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1036293 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1036291 y x z) (@lem1036292 y z)). Qed.
Lemma lem1036294 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1036276 x y z) (@lem1036293 x y z)). Qed.
Lemma lem1036296 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term413 d' w.
Proof. exact (conj (@lem1036175 w d' h1) (@lem1036183 w)). Qed.
Lemma lem1036298 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1036294 x y z) (@lem1036273 y x z)). Qed.
Lemma lem1036299 (d' : nat) (w : nat) : term414 d' w.
Proof. exact (@lem1036298 w (Nat.add w d') w). Qed.
Lemma lem1036302 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : (Nat.add w d') = w.
Proof. exact (@lem1036299 d' w (@lem1036296 w d' h1)). Qed.
Lemma lem1036303 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term405 d' w.
Proof. exact (fun h0 : term349 d' w => @lem1036302 w d' h1). Qed.
Lemma lem1036305 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036306 (d' : nat) (w : nat) : (term405 d' w) = ((Nat.add w d') = w).
Proof. exact (@lem1036305 ((Nat.add w d') = w)). Qed.
Lemma lem1036307 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : (Nat.add w d') = w.
Proof. exact (EQ_MP (@lem1036306 d' w) (@lem1036303 w d' h1)). Qed.
Lemma lem1036325 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036326 (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term415 _17119 _17123 _17122 _17120 _17121) = (term416 _17122 _17123 _17119 _17120 _17121).
Proof. exact (@lem1036325 ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122)) (term296 _17122 _17123 _17119) (term260 _17120 _17121)). Qed.
Lemma lem1036342 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036343 (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term417 _17122 _17123 _17119 _17120 _17121) = (term418 _17120 _17121 _17122 _17123 _17119).
Proof. exact (@lem1036342 (term260 _17120 _17121) (term296 _17122 _17123 _17119)). Qed.
Lemma lem1036353 (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term236 _17120 _17123 _17121 _17122) = (term236 _17120 _17123 _17121 _17122).
Proof. exact (eq_refl (term236 _17120 _17123 _17121 _17122)). Qed.
Lemma lem1036354 (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term416 _17122 _17123 _17119 _17120 _17121) = (term419 _17120 _17121 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036353 _17120 _17123 _17121 _17122) (@lem1036343 _17120 _17121 _17122 _17123 _17119)). Qed.
Lemma lem1036365 (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term415 _17119 _17123 _17122 _17120 _17121) = (term419 _17120 _17121 _17122 _17123 _17119).
Proof. exact (TRANS (@lem1036326 _17122 _17123 _17119 _17120 _17121) (@lem1036354 _17120 _17121 _17122 _17123 _17119)). Qed.
Lemma lem1036366 (_17120 : nat) (_17121 : nat) (_17118 : nat) : (term356 _17120 _17121 _17118) = (term356 _17120 _17121 _17118).
Proof. exact (eq_refl (term356 _17120 _17121 _17118)). Qed.
Lemma lem1036367 (_17118 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term420 _17118 _17120 _17121 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036366 _17120 _17121 _17118) (@lem1036365 _17120 _17121 _17122 _17123 _17119)). Qed.
Lemma lem1036371 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036372 (_17118 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term420 _17118 _17120 _17121 _17122 _17123 _17119) = (term421 _17118 _17120 _17121 _17122 _17123 _17119).
Proof. exact (@lem1036371 ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122)) (term296 _17120 _17121 _17118) (term418 _17120 _17121 _17122 _17123 _17119)). Qed.
Lemma lem1036388 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036389 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term422 _17118 _17120 _17121 _17122 _17123 _17119) = (term423 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (@lem1036388 (term260 _17120 _17121) (term296 _17120 _17121 _17118) (term296 _17122 _17123 _17119)). Qed.
Lemma lem1036411 (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term236 _17120 _17123 _17121 _17122) = (term236 _17120 _17123 _17121 _17122).
Proof. exact (eq_refl (term236 _17120 _17123 _17121 _17122)). Qed.
Lemma lem1036412 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term421 _17118 _17120 _17121 _17122 _17123 _17119) = (term424 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036411 _17120 _17123 _17121 _17122) (@lem1036389 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036423 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term420 _17118 _17120 _17121 _17122 _17123 _17119) = (term424 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (TRANS (@lem1036372 _17118 _17120 _17121 _17122 _17123 _17119) (@lem1036412 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036424 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term424 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (TRANS (@lem1036367 _17118 _17120 _17121 _17122 _17123 _17119) (@lem1036423 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1036426 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term425 _17118 _17119 _17123 _17122 _17120 _17121) = (term426 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036425) (@lem1036424 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036455 (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term417 _17122 _17123 _17119 _17120 _17121) = (term418 _17120 _17121 _17122 _17123 _17119).
Proof. exact (@lem1036454 (term260 _17120 _17121) (term296 _17122 _17123 _17119)). Qed.
Lemma lem1036465 (_17120 : nat) (_17121 : nat) (_17118 : nat) : (term356 _17120 _17121 _17118) = (term356 _17120 _17121 _17118).
Proof. exact (eq_refl (term356 _17120 _17121 _17118)). Qed.
Lemma lem1036466 (_17118 : nat) (_17120 : nat) (_17121 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term427 _17118 _17122 _17123 _17119 _17120 _17121) = (term422 _17118 _17120 _17121 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036465 _17120 _17121 _17118) (@lem1036455 _17120 _17121 _17122 _17123 _17119)). Qed.
Lemma lem1036470 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036471 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term422 _17118 _17120 _17121 _17122 _17123 _17119) = (term423 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (@lem1036470 (term260 _17120 _17121) (term296 _17120 _17121 _17118) (term296 _17122 _17123 _17119)). Qed.
Lemma lem1036493 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term427 _17118 _17122 _17123 _17119 _17120 _17121) = (term423 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (TRANS (@lem1036466 _17118 _17120 _17121 _17122 _17123 _17119) (@lem1036471 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036494 (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term236 _17120 _17123 _17121 _17122) = (term236 _17120 _17123 _17121 _17122).
Proof. exact (eq_refl (term236 _17120 _17123 _17121 _17122)). Qed.
Lemma lem1036495 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term428 _17118 _17122 _17123 _17119 _17120 _17121) = (term424 _17120 _17121 _17118 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036494 _17120 _17123 _17121 _17122) (@lem1036493 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036506 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : ((term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term428 _17118 _17122 _17123 _17119 _17120 _17121)) = ((term424 _17120 _17121 _17118 _17122 _17123 _17119) = (term424 _17120 _17121 _17118 _17122 _17123 _17119)).
Proof. exact (MK_COMB (@lem1036426 _17120 _17121 _17118 _17122 _17123 _17119) (@lem1036495 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036508 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1036509 (x : Prop) : (x = x) = True.
Proof. exact (@lem1036508 Prop x). Qed.
Lemma lem1036510 (_17120 : nat) (_17121 : nat) (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) : ((term424 _17120 _17121 _17118 _17122 _17123 _17119) = (term424 _17120 _17121 _17118 _17122 _17123 _17119)) = True.
Proof. exact (@lem1036509 (term424 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036511 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : ((term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term428 _17118 _17122 _17123 _17119 _17120 _17121)) = True.
Proof. exact (TRANS (@lem1036506 _17120 _17121 _17118 _17122 _17123 _17119) (@lem1036510 _17120 _17121 _17118 _17122 _17123 _17119)). Qed.
Lemma lem1036512 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : True = ((term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term428 _17118 _17122 _17123 _17119 _17120 _17121)).
Proof. exact (SYM (@lem1036511 _17118 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036513 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term298 _17118 _17119 _17123 _17122 _17120 _17121) = (term428 _17118 _17122 _17123 _17119 _17120 _17121).
Proof. exact (EQ_MP (@lem1036512 _17118 _17122 _17123 _17119 _17120 _17121) (@lem0)). Qed.
Lemma lem1036514 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) (h1 : term107) : term428 _17118 _17122 _17123 _17119 _17120 _17121.
Proof. exact (EQ_MP (@lem1036513 _17118 _17122 _17123 _17119 _17120 _17121) (@lem1035316 _17118 _17119 _17123 _17122 _17120 _17121 h1)). Qed.
Lemma lem1036516 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1036517 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term428 _17118 _17122 _17123 _17119 _17120 _17121) = (term429 _17118 _17119 _17120 _17123 _17121 _17122).
Proof. exact (@lem1036516 (term427 _17118 _17122 _17123 _17119 _17120 _17121) ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122))). Qed.
Lemma lem1036519 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036520 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term430 _17118 _17122 _17123 _17119 _17120 _17121) = (term431 _17118 _17122 _17123 _17119 _17120 _17121).
Proof. exact (@lem1036519 (term296 _17120 _17121 _17118) (term417 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036522 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036523 (_17120 : nat) (_17121 : nat) (_17118 : nat) : (term385 _17120 _17121 _17118) = (_17120 = (Nat.add _17121 _17118)).
Proof. exact (@lem1036522 (_17120 = (Nat.add _17121 _17118))). Qed.
Lemma lem1036524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036525 (_17120 : nat) (_17121 : nat) (_17118 : nat) : (term386 _17120 _17121 _17118) = (term387 _17120 _17121 _17118).
Proof. exact (MK_COMB (@lem1036524) (@lem1036523 _17120 _17121 _17118)). Qed.
Lemma lem1036527 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036528 (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term432 _17122 _17123 _17119 _17120 _17121) = (term433 _17122 _17123 _17119 _17120 _17121).
Proof. exact (@lem1036527 (term296 _17122 _17123 _17119) (term260 _17120 _17121)). Qed.
Lemma lem1036530 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036531 (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term385 _17122 _17123 _17119) = (_17122 = (Nat.add _17123 _17119)).
Proof. exact (@lem1036530 (_17122 = (Nat.add _17123 _17119))). Qed.
Lemma lem1036532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036533 (_17122 : nat) (_17123 : nat) (_17119 : nat) : (term386 _17122 _17123 _17119) = (term387 _17122 _17123 _17119).
Proof. exact (MK_COMB (@lem1036532) (@lem1036531 _17122 _17123 _17119)). Qed.
Lemma lem1036535 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036536 (_17120 : nat) (_17121 : nat) : (term321 _17120 _17121) = (_17120 = _17121).
Proof. exact (@lem1036535 (_17120 = _17121)). Qed.
Lemma lem1036537 (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term433 _17122 _17123 _17119 _17120 _17121) = (term434 _17122 _17123 _17119 _17120 _17121).
Proof. exact (MK_COMB (@lem1036533 _17122 _17123 _17119) (@lem1036536 _17120 _17121)). Qed.
Lemma lem1036538 (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term432 _17122 _17123 _17119 _17120 _17121) = (term434 _17122 _17123 _17119 _17120 _17121).
Proof. exact (TRANS (@lem1036528 _17122 _17123 _17119 _17120 _17121) (@lem1036537 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036539 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term431 _17118 _17122 _17123 _17119 _17120 _17121) = (term435 _17118 _17122 _17123 _17119 _17120 _17121).
Proof. exact (MK_COMB (@lem1036525 _17120 _17121 _17118) (@lem1036538 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036540 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term430 _17118 _17122 _17123 _17119 _17120 _17121) = (term435 _17118 _17122 _17123 _17119 _17120 _17121).
Proof. exact (TRANS (@lem1036520 _17118 _17122 _17123 _17119 _17120 _17121) (@lem1036539 _17118 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1036542 (_17118 : nat) (_17122 : nat) (_17123 : nat) (_17119 : nat) (_17120 : nat) (_17121 : nat) : (term436 _17118 _17122 _17123 _17119 _17120 _17121) = (term437 _17118 _17122 _17123 _17119 _17120 _17121).
Proof. exact (MK_COMB (@lem1036541) (@lem1036540 _17118 _17122 _17123 _17119 _17120 _17121)). Qed.
Lemma lem1036543 (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122)) = ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122)).
Proof. exact (eq_refl ((term53 _17120 _17122 _17121 _17123) = (term53 _17120 _17123 _17121 _17122))). Qed.
Lemma lem1036544 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term429 _17118 _17119 _17120 _17123 _17121 _17122) = (term438 _17118 _17119 _17120 _17123 _17121 _17122).
Proof. exact (MK_COMB (@lem1036542 _17118 _17122 _17123 _17119 _17120 _17121) (@lem1036543 _17120 _17123 _17121 _17122)). Qed.
Lemma lem1036545 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) : (term428 _17118 _17122 _17123 _17119 _17120 _17121) = (term438 _17118 _17119 _17120 _17123 _17121 _17122).
Proof. exact (TRANS (@lem1036517 _17118 _17119 _17120 _17123 _17121 _17122) (@lem1036544 _17118 _17119 _17120 _17123 _17121 _17122)). Qed.
Lemma lem1036547 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term439 y d d' w.
Proof. exact (conj (@lem1036168 y d) (@lem1036307 w d' h1)). Qed.
Lemma lem1036548 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term440 y d d' w.
Proof. exact (conj (@lem1036160 w d') (@lem1036547 y d w d' h1)). Qed.
Lemma lem1036550 (_17118 : nat) (_17119 : nat) (_17120 : nat) (_17123 : nat) (_17121 : nat) (_17122 : nat) (h1 : term107) : term438 _17118 _17119 _17120 _17123 _17121 _17122.
Proof. exact (EQ_MP (@lem1036545 _17118 _17119 _17120 _17123 _17121 _17122) (@lem1036514 _17118 _17122 _17123 _17119 _17120 _17121 h1)). Qed.
Lemma lem1036551 (d' : nat) (w : nat) (y : nat) (d : nat) (h1 : term107) : term441 d' w y d.
Proof. exact (@lem1036550 d' d (Nat.add w d') y w (Nat.add y d) h1). Qed.
Lemma lem1036554 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : (term54 d' d w y) = (term58 d' w y d).
Proof. exact (@lem1036551 d' w y d h1 (@lem1036548 y d w d' h2)). Qed.
Lemma lem1036555 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : term336 d' w y d.
Proof. exact (fun h0 : term337 d' w y d => @lem1036554 y d w d' h1 h2). Qed.
Lemma lem1036557 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036558 (d' : nat) (w : nat) (y : nat) (d : nat) : (term336 d' w y d) = ((term54 d' d w y) = (term58 d' w y d)).
Proof. exact (@lem1036557 ((term54 d' d w y) = (term58 d' w y d))). Qed.
Lemma lem1036559 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : (term54 d' d w y) = (term58 d' w y d).
Proof. exact (EQ_MP (@lem1036558 d' w y d) (@lem1036555 y d w d' h1 h2)). Qed.
Lemma lem1036561 (_17117 : nat) (_17116 : nat) (h1 : term216) : (Nat.add _17116 _17117) = (Nat.add _17117 _17116).
Proof. exact (EQ_MP (@lem1035149 _17117 _17116) (@lem1035148 _17116 _17117 h1)). Qed.
Lemma lem1036562 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) : (term54 d' d w y) = (term149 w d' y d).
Proof. exact (@lem1036561 (Nat.mul w y) (term50 w d' y d) h1). Qed.
Lemma lem1036563 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) : term442 w d' y d.
Proof. exact (fun h0 : term443 w d' y d => @lem1036562 w d' y d h1). Qed.
Lemma lem1036565 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036566 (w : nat) (d' : nat) (y : nat) (d : nat) : (term442 w d' y d) = ((term54 d' d w y) = (term149 w d' y d)).
Proof. exact (@lem1036565 ((term54 d' d w y) = (term149 w d' y d))). Qed.
Lemma lem1036567 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) : (term54 d' d w y) = (term149 w d' y d).
Proof. exact (EQ_MP (@lem1036566 w d' y d) (@lem1036563 w d' y d h1)). Qed.
Lemma lem1036568 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term444 w d' y d.
Proof. exact (conj (@lem1036559 y d w d' h1 h3) (@lem1036567 w d' y d h2)). Qed.
Lemma lem1036570 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1036294 x y z) (@lem1036273 y x z)). Qed.
Lemma lem1036571 (w : nat) (d' : nat) (y : nat) (d : nat) : term445 w d' y d.
Proof. exact (@lem1036570 (term54 d' d w y) (term58 d' w y d) (term149 w d' y d)). Qed.
Lemma lem1036574 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term58 d' w y d) = (term149 w d' y d).
Proof. exact (@lem1036571 w d' y d (@lem1036568 y d w d' h1 h2 h3)). Qed.
Lemma lem1036575 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term446 w d' y d.
Proof. exact (fun h0 : term447 w d' y d => @lem1036574 y d w d' h1 h2 h3). Qed.
Lemma lem1036577 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036578 (w : nat) (d' : nat) (y : nat) (d : nat) : (term446 w d' y d) = ((term58 d' w y d) = (term149 w d' y d)).
Proof. exact (@lem1036577 ((term58 d' w y d) = (term149 w d' y d))). Qed.
Lemma lem1036579 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term58 d' w y d) = (term149 w d' y d).
Proof. exact (EQ_MP (@lem1036578 w d' y d) (@lem1036575 y d w d' h1 h2 h3)). Qed.
Lemma lem1036581 (_17117 : nat) (_17116 : nat) (h1 : term216) : (Nat.add _17116 _17117) = (Nat.add _17117 _17116).
Proof. exact (EQ_MP (@lem1035149 _17117 _17116) (@lem1035148 _17116 _17117 h1)). Qed.
Lemma lem1036582 (d : nat) (w : nat) (d' : nat) (y : nat) (h1 : term216) : (term58 d' w y d) = (term150 d w d' y).
Proof. exact (@lem1036581 (term46 w y d) (term39 w d' y) h1). Qed.
Lemma lem1036583 (d : nat) (w : nat) (d' : nat) (y : nat) (h1 : term216) : term448 d w d' y.
Proof. exact (fun h0 : term449 d w d' y => @lem1036582 d w d' y h1). Qed.
Lemma lem1036585 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036586 (d : nat) (w : nat) (d' : nat) (y : nat) : (term448 d w d' y) = ((term58 d' w y d) = (term150 d w d' y)).
Proof. exact (@lem1036585 ((term58 d' w y d) = (term150 d w d' y))). Qed.
Lemma lem1036587 (d : nat) (w : nat) (d' : nat) (y : nat) (h1 : term216) : (term58 d' w y d) = (term150 d w d' y).
Proof. exact (EQ_MP (@lem1036586 d w d' y) (@lem1036583 d w d' y h1)). Qed.
Lemma lem1036588 (d : nat) (y : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term450 d w d' y.
Proof. exact (conj (@lem1036579 y d w d' h1 h2 h3) (@lem1036587 d w d' y h2)). Qed.
Lemma lem1036590 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1036294 x y z) (@lem1036273 y x z)). Qed.
Lemma lem1036591 (d : nat) (w : nat) (d' : nat) (y : nat) : term451 d w d' y.
Proof. exact (@lem1036590 (term58 d' w y d) (term149 w d' y d) (term150 d w d' y)). Qed.
Lemma lem1036594 (d : nat) (y : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (@lem1036591 d w d' y (@lem1036588 d y w d' h1 h2 h3)). Qed.
Lemma lem1036595 (d : nat) (y : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term303 d w d' y.
Proof. exact (fun h0 : term297 d w d' y => @lem1036594 d y w d' h1 h2 h3). Qed.
Lemma lem1036597 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036598 (d : nat) (w : nat) (d' : nat) (y : nat) : (term303 d w d' y) = ((term149 w d' y d) = (term150 d w d' y)).
Proof. exact (@lem1036597 ((term149 w d' y d) = (term150 d w d' y))). Qed.
Lemma lem1036599 (d : nat) (y : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (EQ_MP (@lem1036598 d w d' y) (@lem1036595 d y w d' h1 h2 h3)). Qed.
Lemma lem1036602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1036604 (d : nat) (w : nat) (d' : nat) (y : nat) : (term297 d w d' y) = (term452 d w d' y).
Proof. exact (@lem1036602 ((term149 w d' y d) = (term150 d w d' y))). Qed.
Lemma lem1036607 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term452 d w d' y.
Proof. exact (EQ_MP (@lem1036604 d w d' y) (@lem1035278 w d' y d h1)). Qed.
Lemma lem1036610 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (@lem1036607 w d' y d h3 (@lem1036599 d y w d' h1 h2 h4)). Qed.
Lemma lem1036611 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : term410.
Proof. exact (fun h0 : ~ False => @lem1036610 y d w d' h1 h2 h3 h4). Qed.
Lemma lem1036613 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036614 : term410 = False.
Proof. exact (@lem1036613 False). Qed.
Lemma lem1036615 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1036614) (@lem1036611 y d w d' h1 h2 h3 h4)). Qed.
Lemma lem1036616 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1036617 (_17150 : nat) (_17152 : nat) (h1 : _17150 = _17152) : _17150 = _17152.
Proof. exact (h1). Qed.
Lemma lem1036618 (_17151 : nat) (_17153 : nat) (h1 : _17151 = _17153) : _17151 = _17153.
Proof. exact (h1). Qed.
Lemma lem1036619 (_17150 : nat) (_17152 : nat) (h1 : _17150 = _17152) : (Nat.add _17150) = (Nat.add _17152).
Proof. exact (MK_COMB (@lem1036616) (@lem1036617 _17150 _17152 h1)). Qed.
Lemma lem1036620 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) (h1 : _17150 = _17152) (h2 : _17151 = _17153) : (Nat.add _17150 _17151) = (Nat.add _17152 _17153).
Proof. exact (MK_COMB (@lem1036619 _17150 _17152 h1) (@lem1036618 _17151 _17153 h2)). Qed.
Lemma lem1036621 (_17151 : nat) (_17153 : nat) (_17150 : nat) (_17152 : nat) (h1 : _17150 = _17152) : term453 _17150 _17151 _17152 _17153.
Proof. exact (fun h0 : _17151 = _17153 => @lem1036620 _17150 _17152 _17151 _17153 h1 h0). Qed.
Lemma lem1036623 (a : Prop) (b : Prop) : (a -> b) = (term454 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1036624 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : (term453 _17150 _17151 _17152 _17153) = (term455 _17150 _17151 _17152 _17153).
Proof. exact (@lem1036623 (_17151 = _17153) ((Nat.add _17150 _17151) = (Nat.add _17152 _17153))). Qed.
Lemma lem1036625 (_17151 : nat) (_17153 : nat) (_17150 : nat) (_17152 : nat) (h1 : _17150 = _17152) : term455 _17150 _17151 _17152 _17153.
Proof. exact (EQ_MP (@lem1036624 _17150 _17151 _17152 _17153) (@lem1036621 _17151 _17153 _17150 _17152 h1)). Qed.
Lemma lem1036626 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : term456 _17150 _17151 _17152 _17153.
Proof. exact (fun h0 : _17150 = _17152 => @lem1036625 _17151 _17153 _17150 _17152 h0). Qed.
Lemma lem1036628 (a : Prop) (b : Prop) : (a -> b) = (term454 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1036629 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : (term456 _17150 _17151 _17152 _17153) = (term457 _17150 _17151 _17152 _17153).
Proof. exact (@lem1036628 (_17150 = _17152) (term455 _17150 _17151 _17152 _17153)). Qed.
Lemma lem1036630 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : term457 _17150 _17151 _17152 _17153.
Proof. exact (EQ_MP (@lem1036629 _17150 _17151 _17152 _17153) (@lem1036626 _17150 _17151 _17152 _17153)). Qed.
Lemma lem1036631 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1036632 (_17154 : nat) (_17156 : nat) (h1 : _17154 = _17156) : _17154 = _17156.
Proof. exact (h1). Qed.
Lemma lem1036633 (_17155 : nat) (_17157 : nat) (h1 : _17155 = _17157) : _17155 = _17157.
Proof. exact (h1). Qed.
Lemma lem1036634 (_17154 : nat) (_17156 : nat) (h1 : _17154 = _17156) : (Nat.mul _17154) = (Nat.mul _17156).
Proof. exact (MK_COMB (@lem1036631) (@lem1036632 _17154 _17156 h1)). Qed.
Lemma lem1036635 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) (h1 : _17154 = _17156) (h2 : _17155 = _17157) : (Nat.mul _17154 _17155) = (Nat.mul _17156 _17157).
Proof. exact (MK_COMB (@lem1036634 _17154 _17156 h1) (@lem1036633 _17155 _17157 h2)). Qed.
Lemma lem1036636 (_17155 : nat) (_17157 : nat) (_17154 : nat) (_17156 : nat) (h1 : _17154 = _17156) : term458 _17154 _17155 _17156 _17157.
Proof. exact (fun h0 : _17155 = _17157 => @lem1036635 _17154 _17156 _17155 _17157 h1 h0). Qed.
Lemma lem1036638 (a : Prop) (b : Prop) : (a -> b) = (term454 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1036639 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : (term458 _17154 _17155 _17156 _17157) = (term459 _17154 _17155 _17156 _17157).
Proof. exact (@lem1036638 (_17155 = _17157) ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157))). Qed.
Lemma lem1036640 (_17155 : nat) (_17157 : nat) (_17154 : nat) (_17156 : nat) (h1 : _17154 = _17156) : term459 _17154 _17155 _17156 _17157.
Proof. exact (EQ_MP (@lem1036639 _17154 _17155 _17156 _17157) (@lem1036636 _17155 _17157 _17154 _17156 h1)). Qed.
Lemma lem1036641 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : term460 _17154 _17155 _17156 _17157.
Proof. exact (fun h0 : _17154 = _17156 => @lem1036640 _17155 _17157 _17154 _17156 h0). Qed.
Lemma lem1036643 (a : Prop) (b : Prop) : (a -> b) = (term454 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1036644 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : (term460 _17154 _17155 _17156 _17157) = (term461 _17154 _17155 _17156 _17157).
Proof. exact (@lem1036643 (_17154 = _17156) (term459 _17154 _17155 _17156 _17157)). Qed.
Lemma lem1036645 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : term461 _17154 _17155 _17156 _17157.
Proof. exact (EQ_MP (@lem1036644 _17154 _17155 _17156 _17157) (@lem1036641 _17154 _17155 _17156 _17157)). Qed.
Lemma lem1036647 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1036649 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036650 (w : nat) : w = w.
Proof. exact (@lem1036649 w). Qed.
Lemma lem1036651 (w : nat) : term411 w.
Proof. exact (fun h0 : term412 w => @lem1036650 w). Qed.
Lemma lem1036653 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036654 (w : nat) : (term411 w) = (w = w).
Proof. exact (@lem1036653 (w = w)). Qed.
Lemma lem1036655 (w : nat) : w = w.
Proof. exact (EQ_MP (@lem1036654 w) (@lem1036651 w)). Qed.
Lemma lem1036657 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1036658 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term408 y d.
Proof. exact (fun h0 : term294 y d => @lem1036657 y d h1). Qed.
Lemma lem1036660 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036661 (y : nat) (d : nat) : (term408 y d) = (y = (Nat.add y d)).
Proof. exact (@lem1036660 (y = (Nat.add y d))). Qed.
Lemma lem1036662 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (EQ_MP (@lem1036661 y d) (@lem1036658 y d h1)). Qed.
Lemma lem1036680 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036681 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term459 _17154 _17155 _17156 _17157) = (term462 _17154 _17156 _17155 _17157).
Proof. exact (@lem1036680 ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157)) (term260 _17155 _17157)). Qed.
Lemma lem1036691 (_17154 : nat) (_17156 : nat) : (term308 _17154 _17156) = (term308 _17154 _17156).
Proof. exact (eq_refl (term308 _17154 _17156)). Qed.
Lemma lem1036692 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term461 _17154 _17155 _17156 _17157) = (term463 _17154 _17156 _17155 _17157).
Proof. exact (MK_COMB (@lem1036691 _17154 _17156) (@lem1036681 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036696 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036697 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term463 _17154 _17156 _17155 _17157) = (term464 _17154 _17156 _17155 _17157).
Proof. exact (@lem1036696 ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157)) (term260 _17154 _17156) (term260 _17155 _17157)). Qed.
Lemma lem1036719 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term461 _17154 _17155 _17156 _17157) = (term464 _17154 _17156 _17155 _17157).
Proof. exact (TRANS (@lem1036692 _17154 _17156 _17155 _17157) (@lem1036697 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1036721 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term465 _17154 _17155 _17156 _17157) = (term466 _17154 _17156 _17155 _17157).
Proof. exact (MK_COMB (@lem1036720) (@lem1036719 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036743 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term464 _17154 _17156 _17155 _17157) = (term464 _17154 _17156 _17155 _17157).
Proof. exact (eq_refl (term464 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036744 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : ((term461 _17154 _17155 _17156 _17157) = (term464 _17154 _17156 _17155 _17157)) = ((term464 _17154 _17156 _17155 _17157) = (term464 _17154 _17156 _17155 _17157)).
Proof. exact (MK_COMB (@lem1036721 _17154 _17156 _17155 _17157) (@lem1036743 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036746 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1036747 (x : Prop) : (x = x) = True.
Proof. exact (@lem1036746 Prop x). Qed.
Lemma lem1036748 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : ((term464 _17154 _17156 _17155 _17157) = (term464 _17154 _17156 _17155 _17157)) = True.
Proof. exact (@lem1036747 (term464 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036749 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : ((term461 _17154 _17155 _17156 _17157) = (term464 _17154 _17156 _17155 _17157)) = True.
Proof. exact (TRANS (@lem1036744 _17154 _17156 _17155 _17157) (@lem1036748 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036750 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : True = ((term461 _17154 _17155 _17156 _17157) = (term464 _17154 _17156 _17155 _17157)).
Proof. exact (SYM (@lem1036749 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036751 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term461 _17154 _17155 _17156 _17157) = (term464 _17154 _17156 _17155 _17157).
Proof. exact (EQ_MP (@lem1036750 _17154 _17156 _17155 _17157) (@lem0)). Qed.
Lemma lem1036752 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : term464 _17154 _17156 _17155 _17157.
Proof. exact (EQ_MP (@lem1036751 _17154 _17156 _17155 _17157) (@lem1036645 _17154 _17155 _17156 _17157)). Qed.
Lemma lem1036754 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1036755 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : (term464 _17154 _17156 _17155 _17157) = (term467 _17154 _17155 _17156 _17157).
Proof. exact (@lem1036754 (term468 _17154 _17156 _17155 _17157) ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157))). Qed.
Lemma lem1036757 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036758 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term469 _17154 _17156 _17155 _17157) = (term470 _17154 _17156 _17155 _17157).
Proof. exact (@lem1036757 (term260 _17154 _17156) (term260 _17155 _17157)). Qed.
Lemma lem1036760 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036761 (_17154 : nat) (_17156 : nat) : (term321 _17154 _17156) = (_17154 = _17156).
Proof. exact (@lem1036760 (_17154 = _17156)). Qed.
Lemma lem1036762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036763 (_17154 : nat) (_17156 : nat) : (term322 _17154 _17156) = (term323 _17154 _17156).
Proof. exact (MK_COMB (@lem1036762) (@lem1036761 _17154 _17156)). Qed.
Lemma lem1036765 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036766 (_17155 : nat) (_17157 : nat) : (term321 _17155 _17157) = (_17155 = _17157).
Proof. exact (@lem1036765 (_17155 = _17157)). Qed.
Lemma lem1036767 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term470 _17154 _17156 _17155 _17157) = (term471 _17154 _17156 _17155 _17157).
Proof. exact (MK_COMB (@lem1036763 _17154 _17156) (@lem1036766 _17155 _17157)). Qed.
Lemma lem1036768 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term469 _17154 _17156 _17155 _17157) = (term471 _17154 _17156 _17155 _17157).
Proof. exact (TRANS (@lem1036758 _17154 _17156 _17155 _17157) (@lem1036767 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1036770 (_17154 : nat) (_17156 : nat) (_17155 : nat) (_17157 : nat) : (term472 _17154 _17156 _17155 _17157) = (term473 _17154 _17156 _17155 _17157).
Proof. exact (MK_COMB (@lem1036769) (@lem1036768 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036771 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157)) = ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157)).
Proof. exact (eq_refl ((Nat.mul _17154 _17155) = (Nat.mul _17156 _17157))). Qed.
Lemma lem1036772 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : (term467 _17154 _17155 _17156 _17157) = (term474 _17154 _17155 _17156 _17157).
Proof. exact (MK_COMB (@lem1036770 _17154 _17156 _17155 _17157) (@lem1036771 _17154 _17155 _17156 _17157)). Qed.
Lemma lem1036773 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : (term464 _17154 _17156 _17155 _17157) = (term474 _17154 _17155 _17156 _17157).
Proof. exact (TRANS (@lem1036755 _17154 _17155 _17156 _17157) (@lem1036772 _17154 _17155 _17156 _17157)). Qed.
Lemma lem1036775 (w : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term475 w y d.
Proof. exact (conj (@lem1036655 w) (@lem1036662 y d h1)). Qed.
Lemma lem1036777 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : term474 _17154 _17155 _17156 _17157.
Proof. exact (EQ_MP (@lem1036773 _17154 _17155 _17156 _17157) (@lem1036752 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036778 (w : nat) (y : nat) (d : nat) : term476 w y d.
Proof. exact (@lem1036777 w y w (Nat.add y d)). Qed.
Lemma lem1036781 (w : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (Nat.mul w y) = (term46 w y d).
Proof. exact (@lem1036778 w y d (@lem1036775 w y d h1)). Qed.
Lemma lem1036782 (w : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term477 w y d.
Proof. exact (fun h0 : term478 w y d => @lem1036781 w y d h1). Qed.
Lemma lem1036784 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036785 (w : nat) (y : nat) (d : nat) : (term477 w y d) = ((Nat.mul w y) = (term46 w y d)).
Proof. exact (@lem1036784 ((Nat.mul w y) = (term46 w y d))). Qed.
Lemma lem1036786 (w : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (Nat.mul w y) = (term46 w y d).
Proof. exact (EQ_MP (@lem1036785 w y d) (@lem1036782 w y d h1)). Qed.
Lemma lem1036788 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036789 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1036788 (Nat.add w d')). Qed.
Lemma lem1036790 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1036789 w d'). Qed.
Lemma lem1036792 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036793 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1036792 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1036794 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1036793 w d') (@lem1036790 w d')). Qed.
Lemma lem1036796 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1036797 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term408 y d.
Proof. exact (fun h0 : term294 y d => @lem1036796 y d h1). Qed.
Lemma lem1036799 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036800 (y : nat) (d : nat) : (term408 y d) = (y = (Nat.add y d)).
Proof. exact (@lem1036799 (y = (Nat.add y d))). Qed.
Lemma lem1036801 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (EQ_MP (@lem1036800 y d) (@lem1036797 y d h1)). Qed.
Lemma lem1036802 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term479 w d' y d.
Proof. exact (conj (@lem1036794 w d') (@lem1036801 y d h1)). Qed.
Lemma lem1036804 (_17154 : nat) (_17155 : nat) (_17156 : nat) (_17157 : nat) : term474 _17154 _17155 _17156 _17157.
Proof. exact (EQ_MP (@lem1036773 _17154 _17155 _17156 _17157) (@lem1036752 _17154 _17156 _17155 _17157)). Qed.
Lemma lem1036805 (w : nat) (d' : nat) (y : nat) (d : nat) : term480 w d' y d.
Proof. exact (@lem1036804 (Nat.add w d') y (Nat.add w d') (Nat.add y d)). Qed.
Lemma lem1036808 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term39 w d' y) = (term50 w d' y d).
Proof. exact (@lem1036805 w d' y d (@lem1036802 w d' y d h1)). Qed.
Lemma lem1036809 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term481 w d' y d.
Proof. exact (fun h0 : term482 w d' y d => @lem1036808 w d' y d h1). Qed.
Lemma lem1036811 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036812 (w : nat) (d' : nat) (y : nat) (d : nat) : (term481 w d' y d) = ((term39 w d' y) = (term50 w d' y d)).
Proof. exact (@lem1036811 ((term39 w d' y) = (term50 w d' y d))). Qed.
Lemma lem1036813 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term39 w d' y) = (term50 w d' y d).
Proof. exact (EQ_MP (@lem1036812 w d' y d) (@lem1036809 w d' y d h1)). Qed.
Lemma lem1036815 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1036816 (w : nat) (d' : nat) (y : nat) : (term39 w d' y) = (term39 w d' y).
Proof. exact (@lem1036815 (term39 w d' y)). Qed.
Lemma lem1036817 (w : nat) (d' : nat) (y : nat) : term483 w d' y.
Proof. exact (fun h0 : term484 w d' y => @lem1036816 w d' y). Qed.
Lemma lem1036819 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036820 (w : nat) (d' : nat) (y : nat) : (term483 w d' y) = ((term39 w d' y) = (term39 w d' y)).
Proof. exact (@lem1036819 ((term39 w d' y) = (term39 w d' y))). Qed.
Lemma lem1036821 (w : nat) (d' : nat) (y : nat) : (term39 w d' y) = (term39 w d' y).
Proof. exact (EQ_MP (@lem1036820 w d' y) (@lem1036817 w d' y)). Qed.
Lemma lem1036839 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036840 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1036839 (y = z) (term260 x z)). Qed.
Lemma lem1036850 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1036851 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1036850 x y) (@lem1036840 y x z)). Qed.
Lemma lem1036855 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036856 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1036855 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1036878 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1036851 y x z) (@lem1036856 y x z)). Qed.
Lemma lem1036879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1036880 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1036879) (@lem1036878 y x z)). Qed.
Lemma lem1036902 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1036903 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1036880 y x z) (@lem1036902 y x z)). Qed.
Lemma lem1036905 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1036906 (x : Prop) : (x = x) = True.
Proof. exact (@lem1036905 Prop x). Qed.
Lemma lem1036907 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1036906 (term310 y x z)). Qed.
Lemma lem1036908 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1036903 y x z) (@lem1036907 y x z)). Qed.
Lemma lem1036909 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1036908 y x z)). Qed.
Lemma lem1036910 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1036909 y x z) (@lem0)). Qed.
Lemma lem1036911 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1036910 y x z) (@lem1036647 x y z)). Qed.
Lemma lem1036913 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1036914 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1036913 (term315 y x z) (y = z)). Qed.
Lemma lem1036916 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1036917 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1036916 (term260 x y) (term260 x z)). Qed.
Lemma lem1036919 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036920 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1036919 (x = y)). Qed.
Lemma lem1036921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1036922 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1036921) (@lem1036920 x y)). Qed.
Lemma lem1036924 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1036925 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1036924 (x = z)). Qed.
Lemma lem1036926 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1036922 x y) (@lem1036925 x z)). Qed.
Lemma lem1036927 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1036917 y x z) (@lem1036926 y x z)). Qed.
Lemma lem1036928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1036929 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1036928) (@lem1036927 y x z)). Qed.
Lemma lem1036930 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1036931 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1036929 y x z) (@lem1036930 y z)). Qed.
Lemma lem1036932 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1036914 x y z) (@lem1036931 x y z)). Qed.
Lemma lem1036934 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term485 d w d' y.
Proof. exact (conj (@lem1036813 w d' y d h1) (@lem1036821 w d' y)). Qed.
Lemma lem1036936 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1036932 x y z) (@lem1036911 y x z)). Qed.
Lemma lem1036937 (d : nat) (w : nat) (d' : nat) (y : nat) : term486 d w d' y.
Proof. exact (@lem1036936 (term39 w d' y) (term50 w d' y d) (term39 w d' y)). Qed.
Lemma lem1036940 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term50 w d' y d) = (term39 w d' y).
Proof. exact (@lem1036937 d w d' y (@lem1036934 w d' y d h1)). Qed.
Lemma lem1036941 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term487 d w d' y.
Proof. exact (fun h0 : term488 d w d' y => @lem1036940 w d' y d h1). Qed.
Lemma lem1036943 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1036944 (d : nat) (w : nat) (d' : nat) (y : nat) : (term487 d w d' y) = ((term50 w d' y d) = (term39 w d' y)).
Proof. exact (@lem1036943 ((term50 w d' y d) = (term39 w d' y))). Qed.
Lemma lem1036945 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term50 w d' y d) = (term39 w d' y).
Proof. exact (EQ_MP (@lem1036944 d w d' y) (@lem1036941 w d' y d h1)). Qed.
Lemma lem1036963 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1036964 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term455 _17150 _17151 _17152 _17153) = (term489 _17150 _17152 _17151 _17153).
Proof. exact (@lem1036963 ((Nat.add _17150 _17151) = (Nat.add _17152 _17153)) (term260 _17151 _17153)). Qed.
Lemma lem1036974 (_17150 : nat) (_17152 : nat) : (term308 _17150 _17152) = (term308 _17150 _17152).
Proof. exact (eq_refl (term308 _17150 _17152)). Qed.
Lemma lem1036975 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term457 _17150 _17151 _17152 _17153) = (term490 _17150 _17152 _17151 _17153).
Proof. exact (MK_COMB (@lem1036974 _17150 _17152) (@lem1036964 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1036979 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1036980 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term490 _17150 _17152 _17151 _17153) = (term491 _17150 _17152 _17151 _17153).
Proof. exact (@lem1036979 ((Nat.add _17150 _17151) = (Nat.add _17152 _17153)) (term260 _17150 _17152) (term260 _17151 _17153)). Qed.
Lemma lem1037002 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term457 _17150 _17151 _17152 _17153) = (term491 _17150 _17152 _17151 _17153).
Proof. exact (TRANS (@lem1036975 _17150 _17152 _17151 _17153) (@lem1036980 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1037004 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term492 _17150 _17151 _17152 _17153) = (term493 _17150 _17152 _17151 _17153).
Proof. exact (MK_COMB (@lem1037003) (@lem1037002 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037026 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term491 _17150 _17152 _17151 _17153) = (term491 _17150 _17152 _17151 _17153).
Proof. exact (eq_refl (term491 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037027 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : ((term457 _17150 _17151 _17152 _17153) = (term491 _17150 _17152 _17151 _17153)) = ((term491 _17150 _17152 _17151 _17153) = (term491 _17150 _17152 _17151 _17153)).
Proof. exact (MK_COMB (@lem1037004 _17150 _17152 _17151 _17153) (@lem1037026 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037029 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1037030 (x : Prop) : (x = x) = True.
Proof. exact (@lem1037029 Prop x). Qed.
Lemma lem1037031 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : ((term491 _17150 _17152 _17151 _17153) = (term491 _17150 _17152 _17151 _17153)) = True.
Proof. exact (@lem1037030 (term491 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037032 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : ((term457 _17150 _17151 _17152 _17153) = (term491 _17150 _17152 _17151 _17153)) = True.
Proof. exact (TRANS (@lem1037027 _17150 _17152 _17151 _17153) (@lem1037031 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037033 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : True = ((term457 _17150 _17151 _17152 _17153) = (term491 _17150 _17152 _17151 _17153)).
Proof. exact (SYM (@lem1037032 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037034 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term457 _17150 _17151 _17152 _17153) = (term491 _17150 _17152 _17151 _17153).
Proof. exact (EQ_MP (@lem1037033 _17150 _17152 _17151 _17153) (@lem0)). Qed.
Lemma lem1037035 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : term491 _17150 _17152 _17151 _17153.
Proof. exact (EQ_MP (@lem1037034 _17150 _17152 _17151 _17153) (@lem1036630 _17150 _17151 _17152 _17153)). Qed.
Lemma lem1037037 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1037038 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : (term491 _17150 _17152 _17151 _17153) = (term494 _17150 _17151 _17152 _17153).
Proof. exact (@lem1037037 (term468 _17150 _17152 _17151 _17153) ((Nat.add _17150 _17151) = (Nat.add _17152 _17153))). Qed.
Lemma lem1037040 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1037041 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term469 _17150 _17152 _17151 _17153) = (term470 _17150 _17152 _17151 _17153).
Proof. exact (@lem1037040 (term260 _17150 _17152) (term260 _17151 _17153)). Qed.
Lemma lem1037043 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1037044 (_17150 : nat) (_17152 : nat) : (term321 _17150 _17152) = (_17150 = _17152).
Proof. exact (@lem1037043 (_17150 = _17152)). Qed.
Lemma lem1037045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1037046 (_17150 : nat) (_17152 : nat) : (term322 _17150 _17152) = (term323 _17150 _17152).
Proof. exact (MK_COMB (@lem1037045) (@lem1037044 _17150 _17152)). Qed.
Lemma lem1037048 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1037049 (_17151 : nat) (_17153 : nat) : (term321 _17151 _17153) = (_17151 = _17153).
Proof. exact (@lem1037048 (_17151 = _17153)). Qed.
Lemma lem1037050 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term470 _17150 _17152 _17151 _17153) = (term471 _17150 _17152 _17151 _17153).
Proof. exact (MK_COMB (@lem1037046 _17150 _17152) (@lem1037049 _17151 _17153)). Qed.
Lemma lem1037051 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term469 _17150 _17152 _17151 _17153) = (term471 _17150 _17152 _17151 _17153).
Proof. exact (TRANS (@lem1037041 _17150 _17152 _17151 _17153) (@lem1037050 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1037053 (_17150 : nat) (_17152 : nat) (_17151 : nat) (_17153 : nat) : (term472 _17150 _17152 _17151 _17153) = (term473 _17150 _17152 _17151 _17153).
Proof. exact (MK_COMB (@lem1037052) (@lem1037051 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037054 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : ((Nat.add _17150 _17151) = (Nat.add _17152 _17153)) = ((Nat.add _17150 _17151) = (Nat.add _17152 _17153)).
Proof. exact (eq_refl ((Nat.add _17150 _17151) = (Nat.add _17152 _17153))). Qed.
Lemma lem1037055 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : (term494 _17150 _17151 _17152 _17153) = (term495 _17150 _17151 _17152 _17153).
Proof. exact (MK_COMB (@lem1037053 _17150 _17152 _17151 _17153) (@lem1037054 _17150 _17151 _17152 _17153)). Qed.
Lemma lem1037056 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : (term491 _17150 _17152 _17151 _17153) = (term495 _17150 _17151 _17152 _17153).
Proof. exact (TRANS (@lem1037038 _17150 _17151 _17152 _17153) (@lem1037055 _17150 _17151 _17152 _17153)). Qed.
Lemma lem1037058 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term496 d w d' y.
Proof. exact (conj (@lem1036786 w y d h1) (@lem1036945 w d' y d h1)). Qed.
Lemma lem1037060 (_17150 : nat) (_17151 : nat) (_17152 : nat) (_17153 : nat) : term495 _17150 _17151 _17152 _17153.
Proof. exact (EQ_MP (@lem1037056 _17150 _17151 _17152 _17153) (@lem1037035 _17150 _17152 _17151 _17153)). Qed.
Lemma lem1037061 (d : nat) (w : nat) (d' : nat) (y : nat) : term497 d w d' y.
Proof. exact (@lem1037060 (Nat.mul w y) (term50 w d' y d) (term46 w y d) (term39 w d' y)). Qed.
Lemma lem1037064 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (@lem1037061 d w d' y (@lem1037058 w d' y d h1)). Qed.
Lemma lem1037065 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term303 d w d' y.
Proof. exact (fun h0 : term297 d w d' y => @lem1037064 w d' y d h1). Qed.
Lemma lem1037067 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1037068 (d : nat) (w : nat) (d' : nat) (y : nat) : (term303 d w d' y) = ((term149 w d' y d) = (term150 d w d' y)).
Proof. exact (@lem1037067 ((term149 w d' y d) = (term150 d w d' y))). Qed.
Lemma lem1037069 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (term149 w d' y d) = (term150 d w d' y).
Proof. exact (EQ_MP (@lem1037068 d w d' y) (@lem1037065 w d' y d h1)). Qed.
Lemma lem1037072 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1037074 (d : nat) (w : nat) (d' : nat) (y : nat) : (term297 d w d' y) = (term452 d w d' y).
Proof. exact (@lem1037072 ((term149 w d' y d) = (term150 d w d' y))). Qed.
Lemma lem1037077 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) : term452 d w d' y.
Proof. exact (EQ_MP (@lem1037074 d w d' y) (@lem1035338 w d' y d h1)). Qed.
Lemma lem1037080 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : False.
Proof. exact (@lem1037077 w d' y d h1 (@lem1037069 w d' y d h2)). Qed.
Lemma lem1037081 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : term410.
Proof. exact (fun h0 : ~ False => @lem1037080 w d' y d h1 h2). Qed.
Lemma lem1037083 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1037084 : term410 = False.
Proof. exact (@lem1037083 False). Qed.
Lemma lem1037085 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1037084) (@lem1037081 w d' y d h1 h2)). Qed.
Lemma lem1037086 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h3 : y = (Nat.add y d) => @lem1037085 w d' y d h1 h2) (fun h3 : False => @lem1035340 y d h2)). Qed.
Lemma lem1037087 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1037086 w d' y d h1 h2) (@lem1035340 y d h2)). Qed.
Lemma lem1037088 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1036615 y d w d' h1 h2 h3 h4) (fun h5 : False => @lem1035280 w d' h4)). Qed.
Lemma lem1037089 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1037088 y d w d' h1 h2 h3 h4) (@lem1035280 w d' h4)). Qed.
Lemma lem1037090 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h3 : y = (Nat.add y d) => @lem1037087 w d' y d h1 h2) (fun h3 : False => @lem1035108 y d h2)). Qed.
Lemma lem1037091 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1037090 w d' y d h1 h2) (@lem1035108 y d h2)). Qed.
Lemma lem1037092 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1037089 y d w d' h1 h2 h3 h4) (fun h5 : False => @lem1035002 w d' h4)). Qed.
Lemma lem1037093 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1037092 y d w d' h1 h2 h3 h4) (@lem1035002 w d' h4)). Qed.
Lemma lem1037094 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h3 : y = (Nat.add y d) => @lem1037091 w d' y d h1 h2) (fun h3 : False => @lem1035108 y d h2)). Qed.
Lemma lem1037095 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term223 w d' y d) (h2 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1037094 w d' y d h1 h2) (@lem1035108 y d h2)). Qed.
Lemma lem1037096 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1037093 y d w d' h1 h2 h3 h4) (fun h5 : False => @lem1035002 w d' h4)). Qed.
Lemma lem1037097 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1037096 y d w d' h1 h2 h3 h4) (@lem1035002 w d' h4)). Qed.
Lemma lem1037098 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : term216 = False.
Proof. exact (prop_ext (fun h5 : term216 => @lem1037097 y d w d' h1 h2 h3 h4) (fun h5 : False => @lem1034916 h2)). Qed.
Lemma lem1037099 (y : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1037098 y d w d' h1 h2 h3 h4) (@lem1034916 h2)). Qed.
Lemma lem1037100 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1036120 w d' y d h1 h2 h3) (fun h4 : False => @lem1034806 h2)). Qed.
Lemma lem1037101 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term226 w d' y d) : False.
Proof. exact (EQ_MP (@lem1037100 w d' y d h1 h2 h3) (@lem1034806 h2)). Qed.
Lemma lem1037102 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term223 w d' y d) : False.
Proof. exact (or_elim (@lem1034783 w d' y d h3) (fun h0 : w = (Nat.add w d') => @lem1037099 y d w d' h1 h2 h3 h0) (fun h0 : y = (Nat.add y d) => @lem1037095 w d' y d h3 h0)). Qed.
Lemma lem1037103 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term176 w d' y d) : False.
Proof. exact (or_elim (@lem1034590 w d' y d h3) (fun h0 : term226 w d' y d => @lem1037101 w d' y d h1 h2 h0) (fun h0 : term223 w d' y d => @lem1037102 w d' y d h1 h2 h0)). Qed.
Lemma lem1037104 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term176 w d' y d) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1037103 w d' y d h1 h2 h3) (fun h4 : False => @lem1034630 h2)). Qed.
Lemma lem1037105 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term176 w d' y d) : False.
Proof. exact (EQ_MP (@lem1037104 w d' y d h1 h2 h3) (@lem1034630 h2)). Qed.
Lemma lem1037106 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term176 w d' y d) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1037105 w d' y d h1 h2 h3) (fun h4 : False => @lem1034314 h2)). Qed.
Lemma lem1037107 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term216) (h3 : term176 w d' y d) : False.
Proof. exact (EQ_MP (@lem1037106 w d' y d h1 h2 h3) (@lem1034314 h2)). Qed.
Lemma lem1037108 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term176 w d' y d) : term181.
Proof. exact (fun h0 : term107 => @lem1037107 w d' y d h0 h1 h2). Qed.
Lemma lem1037109 : term181 = term182.
Proof. exact (@lem69 term107). Qed.
Lemma lem1037110 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term216) (h2 : term176 w d' y d) : term182.
Proof. exact (EQ_MP (@lem1037109) (@lem1037108 w d' y d h1 h2)). Qed.
Lemma lem1037111 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term185.
Proof. exact (fun h0 : term216 => @lem1037110 w d' y d h0 h1). Qed.
Lemma lem1037112 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term188.
Proof. exact (fun h0 : term220 => @lem1037111 w d' y d h1). Qed.
Lemma lem1037113 (w : nat) (d' : nat) (y : nat) (d : nat) : term190 w d' y d.
Proof. exact (fun h0 : term176 w d' y d => @lem1037112 w d' y d h0). Qed.
Lemma lem1037118 (d' : nat) (y : nat) (d : nat) : term194 d' y d.
Proof. exact (fun w : nat => @lem1037113 w d' y d). Qed.
Lemma lem1037123 (y : nat) (d : nat) : term198 y d.
Proof. exact (fun d' : nat => @lem1037118 d' y d). Qed.
Lemma lem1037128 (d : nat) : term202 d.
Proof. exact (fun y : nat => @lem1037123 y d). Qed.
Lemma lem1037133 : term206.
Proof. exact (fun d : nat => @lem1037128 d). Qed.
Lemma lem1037134 : term205.
Proof. exact (EQ_MP (@lem1034240) (@lem1037133)). Qed.
Lemma lem1037135 (d : nat) : term498 d.
Proof. exact (@lem1037134 d). Qed.
Lemma lem1037136 (d : nat) : (term498 d) = (term201 d).
Proof. exact (eq_refl (term498 d)). Qed.
Lemma lem1037137 (d : nat) : term201 d.
Proof. exact (EQ_MP (@lem1037136 d) (@lem1037135 d)). Qed.
Lemma lem1037138 (d : nat) (y : nat) : term499 d y.
Proof. exact (@lem1037137 d y). Qed.
Lemma lem1037139 (y : nat) (d : nat) : (term499 d y) = (term197 y d).
Proof. exact (eq_refl (term499 d y)). Qed.
Lemma lem1037140 (y : nat) (d : nat) : term197 y d.
Proof. exact (EQ_MP (@lem1037139 y d) (@lem1037138 d y)). Qed.
Lemma lem1037141 (y : nat) (d : nat) (d' : nat) : term500 y d d'.
Proof. exact (@lem1037140 y d d'). Qed.
Lemma lem1037142 (d' : nat) (y : nat) (d : nat) : (term500 y d d') = (term193 d' y d).
Proof. exact (eq_refl (term500 y d d')). Qed.
Lemma lem1037143 (d' : nat) (y : nat) (d : nat) : term193 d' y d.
Proof. exact (EQ_MP (@lem1037142 d' y d) (@lem1037141 y d d')). Qed.
Lemma lem1037144 (d' : nat) (y : nat) (d : nat) (w : nat) : term501 d' y d w.
Proof. exact (@lem1037143 d' y d w). Qed.
Lemma lem1037145 (w : nat) (d' : nat) (y : nat) (d : nat) : (term501 d' y d w) = (term177 w d' y d).
Proof. exact (eq_refl (term501 d' y d w)). Qed.
Lemma lem1037146 (w : nat) (d' : nat) (y : nat) (d : nat) : term177 w d' y d.
Proof. exact (EQ_MP (@lem1037145 w d' y d) (@lem1037144 d' y d w)). Qed.
Lemma lem1037148 (w : nat) (d' : nat) (y : nat) (d : nat) : term177 w d' y d.
Proof. exact (@lem1033938 w d' y d (@lem1037146 w d' y d)). Qed.
Lemma lem1037149 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term187.
Proof. exact (@lem1037148 w d' y d (@lem1033923 w d' y d h1)). Qed.
Lemma lem1037150 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term184.
Proof. exact (@lem1037149 w d' y d h1 (@lem81820)). Qed.
Lemma lem1037151 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : term181.
Proof. exact (@lem1037150 w d' y d h1 (@lem77775)). Qed.
Lemma lem1037152 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : False.
Proof. exact (@lem1037151 w d' y d h1 (@lem1033477)). Qed.
Lemma lem1037153 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : (term176 w d' y d) = False.
Proof. exact (prop_ext (fun h2 : term176 w d' y d => @lem1037152 w d' y d h1) (fun h2 : False => @lem1033923 w d' y d h1)). Qed.
Lemma lem1037154 (w : nat) (d' : nat) (y : nat) (d : nat) (h1 : term176 w d' y d) : False.
Proof. exact (EQ_MP (@lem1037153 w d' y d h1) (@lem1033923 w d' y d h1)). Qed.
Lemma lem1037155 (w : nat) (d' : nat) (y : nat) (d : nat) : term175 w d' y d.
Proof. exact (fun h0 : term176 w d' y d => @lem1037154 w d' y d h0). Qed.
Lemma lem1037156 (w : nat) (d' : nat) (y : nat) (d : nat) : ((term149 w d' y d) = (term150 d w d' y)) = (term151 w d' y d).
Proof. exact (EQ_MP (@lem1033922 w d' y d) (@lem1037155 w d' y d)). Qed.
Lemma lem1037158 (p : Prop) : p = (term174 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1037159 (w : nat) (d' : nat) (d : nat) (z : nat) : (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)) = (term502 w d' d z).
Proof. exact (@lem1037158 (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z))). Qed.
Lemma lem1037160 (w : nat) (d' : nat) (d : nat) (z : nat) : (term502 w d' d z) = (((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z)).
Proof. exact (SYM (@lem1037159 w d' d z)). Qed.
Lemma lem1037161 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term503 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037164 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term504 w d' d z) : term504 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037165 (w : nat) (d' : nat) (d : nat) (z : nat) : term505 w d' d z.
Proof. exact (fun h0 : term504 w d' d z => @lem1037164 w d' d z h0). Qed.
Lemma lem1037166 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term505 w d' d z) : term505 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037167 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term504 w d' d z) : term504 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037168 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term504 w d' d z) (h2 : term505 w d' d z) : term504 w d' d z.
Proof. exact (@lem1037166 w d' d z h2 (@lem1037167 w d' d z h1)). Qed.
Lemma lem1037169 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term504 w d' d z) : term506 w d' d z.
Proof. exact (fun h0 : term505 w d' d z => @lem1037168 w d' d z h1 h0). Qed.
Lemma lem1037170 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term505 w d' d z) : term505 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037171 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term504 w d' d z) (h2 : term505 w d' d z) : term504 w d' d z.
Proof. exact (@lem1037169 w d' d z h1 (@lem1037170 w d' d z h2)). Qed.
Lemma lem1037172 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term505 w d' d z) : term505 w d' d z.
Proof. exact (fun h0 : term504 w d' d z => @lem1037171 w d' d z h0 h1). Qed.
Lemma lem1037173 (w : nat) (d' : nat) (d : nat) (z : nat) : term507 w d' d z.
Proof. exact (fun h0 : term505 w d' d z => @lem1037172 w d' d z h0). Qed.
Lemma lem1037176 (w : nat) (d' : nat) (d : nat) (z : nat) : term505 w d' d z.
Proof. exact (@lem1037173 w d' d z (@lem1037165 w d' d z)). Qed.
Lemma lem1037218 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1037219 : term181 = term182.
Proof. exact (@lem1037218 term107). Qed.
Lemma lem1037250 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1037251 : term184 = term185.
Proof. exact (MK_COMB (@lem1037250) (@lem1037219)). Qed.
Lemma lem1037254 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem1037255 : term187 = term188.
Proof. exact (MK_COMB (@lem1037254) (@lem1037251)). Qed.
Lemma lem1037258 (w : nat) (d' : nat) (d : nat) (z : nat) : (term508 w d' d z) = (term508 w d' d z).
Proof. exact (eq_refl (term508 w d' d z)). Qed.
Lemma lem1037259 (w : nat) (d' : nat) (d : nat) (z : nat) : (term504 w d' d z) = (term509 w d' d z).
Proof. exact (MK_COMB (@lem1037258 w d' d z) (@lem1037255)). Qed.
Lemma lem1037262 (d' : nat) (d : nat) (z : nat) : (term510 d' d z) = (term511 d' d z).
Proof. exact (fun_ext (fun w : nat => @lem1037259 w d' d z)). Qed.
Lemma lem1037263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037264 (d' : nat) (d : nat) (z : nat) : (term512 d' d z) = (term513 d' d z).
Proof. exact (MK_COMB (@lem1037263) (@lem1037262 d' d z)). Qed.
Lemma lem1037269 (d : nat) (z : nat) : (term514 d z) = (term515 d z).
Proof. exact (fun_ext (fun d' : nat => @lem1037264 d' d z)). Qed.
Lemma lem1037270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037271 (d : nat) (z : nat) : (term516 d z) = (term517 d z).
Proof. exact (MK_COMB (@lem1037270) (@lem1037269 d z)). Qed.
Lemma lem1037276 (z : nat) : (term518 z) = (term519 z).
Proof. exact (fun_ext (fun d : nat => @lem1037271 d z)). Qed.
Lemma lem1037277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037278 (z : nat) : (term520 z) = (term521 z).
Proof. exact (MK_COMB (@lem1037277) (@lem1037276 z)). Qed.
Lemma lem1037283 : term522 = term523.
Proof. exact (fun_ext (fun z : nat => @lem1037278 z)). Qed.
Lemma lem1037284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037293 : term524 = term525.
Proof. exact (MK_COMB (@lem1037284) (@lem1037283)). Qed.
Lemma lem1037310 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term94 d e w x y z).
Proof. exact (eq_refl (term94 d e w x y z)). Qed.
Lemma lem1037311 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term207 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1037310 d e w x y z)). Qed.
Lemma lem1037312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037313 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term102 d e w x y).
Proof. exact (MK_COMB (@lem1037312) (@lem1037311 d e w x y)). Qed.
Lemma lem1037314 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term208 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1037313 d e w x y)). Qed.
Lemma lem1037315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037316 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term103 d e w x).
Proof. exact (MK_COMB (@lem1037315) (@lem1037314 d e w x)). Qed.
Lemma lem1037317 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term209 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1037316 d e w x)). Qed.
Lemma lem1037318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037319 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term104 d e w).
Proof. exact (MK_COMB (@lem1037318) (@lem1037317 d e w)). Qed.
Lemma lem1037320 (d : nat) (e : nat) : (term210 d e) = (term210 d e).
Proof. exact (fun_ext (fun w : nat => @lem1037319 d e w)). Qed.
Lemma lem1037321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037322 (d : nat) (e : nat) : (term105 d e) = (term105 d e).
Proof. exact (MK_COMB (@lem1037321) (@lem1037320 d e)). Qed.
Lemma lem1037323 (d : nat) : (term211 d) = (term211 d).
Proof. exact (fun_ext (fun e : nat => @lem1037322 d e)). Qed.
Lemma lem1037324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037325 (d : nat) : (term106 d) = (term106 d).
Proof. exact (MK_COMB (@lem1037324) (@lem1037323 d)). Qed.
Lemma lem1037326 : term212 = term212.
Proof. exact (fun_ext (fun d : nat => @lem1037325 d)). Qed.
Lemma lem1037327 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037328 : term107 = term107.
Proof. exact (MK_COMB (@lem1037327) (@lem1037326)). Qed.
Lemma lem1037329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1037330 : term182 = term182.
Proof. exact (MK_COMB (@lem1037329) (@lem1037328)). Qed.
Lemma lem1037331 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1037332 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1037331 n m)). Qed.
Lemma lem1037333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037334 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1037333) (@lem1037332 m)). Qed.
Lemma lem1037335 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1037334 m)). Qed.
Lemma lem1037336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037337 : term216 = term216.
Proof. exact (MK_COMB (@lem1037336) (@lem1037335)). Qed.
Lemma lem1037338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1037339 : term183 = term183.
Proof. exact (MK_COMB (@lem1037338) (@lem1037337)). Qed.
Lemma lem1037340 : term185 = term185.
Proof. exact (MK_COMB (@lem1037339) (@lem1037330)). Qed.
Lemma lem1037341 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1037342 (m : nat) : (term217 m) = (term217 m).
Proof. exact (fun_ext (fun n : nat => @lem1037341 n m)). Qed.
Lemma lem1037343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037344 (m : nat) : (term218 m) = (term218 m).
Proof. exact (MK_COMB (@lem1037343) (@lem1037342 m)). Qed.
Lemma lem1037345 : term219 = term219.
Proof. exact (fun_ext (fun m : nat => @lem1037344 m)). Qed.
Lemma lem1037346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037347 : term220 = term220.
Proof. exact (MK_COMB (@lem1037346) (@lem1037345)). Qed.
Lemma lem1037348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1037349 : term186 = term186.
Proof. exact (MK_COMB (@lem1037348) (@lem1037347)). Qed.
Lemma lem1037350 : term188 = term188.
Proof. exact (MK_COMB (@lem1037349) (@lem1037340)). Qed.
Lemma lem1037363 (w : nat) (d' : nat) (d : nat) (z : nat) : (term508 w d' d z) = (term508 w d' d z).
Proof. exact (eq_refl (term508 w d' d z)). Qed.
Lemma lem1037364 (w : nat) (d' : nat) (d : nat) (z : nat) : (term509 w d' d z) = (term509 w d' d z).
Proof. exact (MK_COMB (@lem1037363 w d' d z) (@lem1037350)). Qed.
Lemma lem1037365 (d' : nat) (d : nat) (z : nat) : (term511 d' d z) = (term511 d' d z).
Proof. exact (fun_ext (fun w : nat => @lem1037364 w d' d z)). Qed.
Lemma lem1037366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037367 (d' : nat) (d : nat) (z : nat) : (term513 d' d z) = (term513 d' d z).
Proof. exact (MK_COMB (@lem1037366) (@lem1037365 d' d z)). Qed.
Lemma lem1037368 (d : nat) (z : nat) : (term515 d z) = (term515 d z).
Proof. exact (fun_ext (fun d' : nat => @lem1037367 d' d z)). Qed.
Lemma lem1037369 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037370 (d : nat) (z : nat) : (term517 d z) = (term517 d z).
Proof. exact (MK_COMB (@lem1037369) (@lem1037368 d z)). Qed.
Lemma lem1037371 (z : nat) : (term519 z) = (term519 z).
Proof. exact (fun_ext (fun d : nat => @lem1037370 d z)). Qed.
Lemma lem1037372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037373 (z : nat) : (term521 z) = (term521 z).
Proof. exact (MK_COMB (@lem1037372) (@lem1037371 z)). Qed.
Lemma lem1037374 : term523 = term523.
Proof. exact (fun_ext (fun z : nat => @lem1037373 z)). Qed.
Lemma lem1037375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037376 : term525 = term525.
Proof. exact (MK_COMB (@lem1037375) (@lem1037374)). Qed.
Lemma lem1037477 : term524 = term525.
Proof. exact (TRANS (@lem1037293) (@lem1037376)). Qed.
Lemma lem1037478 : term525 = term524.
Proof. exact (SYM (@lem1037477)). Qed.
Lemma lem1037479 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term503 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1037481 (h1 : term216) : term216.
Proof. exact (h1). Qed.
Lemma lem1037482 (h1 : term107) : term107.
Proof. exact (h1). Qed.
Lemma lem1037493 (w : nat) (d' : nat) (d : nat) (z : nat) : (term526 w d' d z) = (term527 w d' d z).
Proof. exact (@lem17160 (w = (Nat.add w d')) ((Nat.add z d) = z)). Qed.
Lemma lem1037499 (w : nat) (d' : nat) (d : nat) (z : nat) : (term528 w d' d z) = (term528 w d' d z).
Proof. exact (eq_refl (term528 w d' d z)). Qed.
Lemma lem1037501 (w : nat) (d' : nat) (z : nat) (d : nat) : (term529 w d' z d) = (term529 w d' z d).
Proof. exact (eq_refl (term529 w d' z d)). Qed.
Lemma lem1037502 (w : nat) (d' : nat) (d : nat) (z : nat) : (term530 w d' d z) = (term531 w d' d z).
Proof. exact (MK_COMB (@lem1037501 w d' z d) (@lem1037493 w d' d z)). Qed.
Lemma lem1037503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1037504 (w : nat) (d' : nat) (d : nat) (z : nat) : (term532 w d' d z) = (term533 w d' d z).
Proof. exact (MK_COMB (@lem1037503) (@lem1037502 w d' d z)). Qed.
Lemma lem1037505 (w : nat) (d' : nat) (d : nat) (z : nat) : (term534 w d' d z) = (term535 w d' d z).
Proof. exact (MK_COMB (@lem1037504 w d' d z) (@lem1037499 w d' d z)). Qed.
Lemma lem1037506 (w : nat) (d' : nat) (d : nat) (z : nat) : (term503 w d' d z) = (term534 w d' d z).
Proof. exact (@lem17646 ((term150 d w d' z) = (term149 w d' z d)) (term162 w d' d z)). Qed.
Lemma lem1037511 (w : nat) (d' : nat) (d : nat) (z : nat) : (term503 w d' d z) = (term535 w d' d z).
Proof. exact (TRANS (@lem1037506 w d' d z) (@lem1037505 w d' d z)). Qed.
Lemma lem1037533 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1037534 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1037533 n m)). Qed.
Lemma lem1037535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037536 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1037535) (@lem1037534 m)). Qed.
Lemma lem1037537 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1037536 m)). Qed.
Lemma lem1037538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037551 : term216 = term216.
Proof. exact (MK_COMB (@lem1037538) (@lem1037537)). Qed.
Lemma lem1037552 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1037551) (@lem1037481 h1)). Qed.
Lemma lem1037559 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term231 w x d y z e) = (term232 w x d y z e).
Proof. exact (@lem17045 (w = (Nat.add x d)) (y = (Nat.add z e))). Qed.
Lemma lem1037570 (w : nat) (x : nat) (y : nat) (z : nat) : (term233 w x y z) = (term234 w x y z).
Proof. exact (@lem17160 (w = x) (y = z)). Qed.
Lemma lem1037576 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1037578 (w : nat) (z : nat) (x : nat) (y : nat) : (term236 w z x y) = (term236 w z x y).
Proof. exact (eq_refl (term236 w z x y)). Qed.
Lemma lem1037579 (w : nat) (x : nat) (y : nat) (z : nat) : (term237 w x y z) = (term238 w x y z).
Proof. exact (MK_COMB (@lem1037578 w z x y) (@lem1037570 w x y z)). Qed.
Lemma lem1037580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1037581 (w : nat) (x : nat) (y : nat) (z : nat) : (term239 w x y z) = (term240 w x y z).
Proof. exact (MK_COMB (@lem1037580) (@lem1037579 w x y z)). Qed.
Lemma lem1037582 (w : nat) (x : nat) (y : nat) (z : nat) : (term241 w x y z) = (term242 w x y z).
Proof. exact (MK_COMB (@lem1037581 w x y z) (@lem1037576 w x y z)). Qed.
Lemma lem1037583 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term241 w x y z).
Proof. exact (@lem17784 ((term53 w y x z) = (term53 w z x y)) (term64 w x y z)). Qed.
Lemma lem1037584 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term242 w x y z).
Proof. exact (TRANS (@lem1037583 w x y z) (@lem1037582 w x y z)). Qed.
Lemma lem1037585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1037586 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term243 w x d y z e) = (term244 w x d y z e).
Proof. exact (MK_COMB (@lem1037585) (@lem1037559 w x d y z e)). Qed.
Lemma lem1037587 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term245 d e w x y z) = (term246 d e w x y z).
Proof. exact (MK_COMB (@lem1037586 w x d y z e) (@lem1037584 w x y z)). Qed.
Lemma lem1037588 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term245 d e w x y z).
Proof. exact (@lem17265 (term48 w x d y z e) (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z))). Qed.
Lemma lem1037589 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term246 d e w x y z).
Proof. exact (TRANS (@lem1037588 d e w x y z) (@lem1037587 d e w x y z)). Qed.
Lemma lem1037590 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1037589 d e w x y z)). Qed.
Lemma lem1037591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037592 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1037591) (@lem1037590 d e w x y)). Qed.
Lemma lem1037593 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1037592 d e w x y)). Qed.
Lemma lem1037594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037595 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1037594) (@lem1037593 d e w x)). Qed.
Lemma lem1037596 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1037595 d e w x)). Qed.
Lemma lem1037597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037598 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1037597) (@lem1037596 d e w)). Qed.
Lemma lem1037599 (d : nat) (e : nat) : (term210 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1037598 d e w)). Qed.
Lemma lem1037600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037601 (d : nat) (e : nat) : (term105 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1037600) (@lem1037599 d e)). Qed.
Lemma lem1037602 (d : nat) : (term211 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1037601 d e)). Qed.
Lemma lem1037603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037604 (d : nat) : (term106 d) = (term256 d).
Proof. exact (MK_COMB (@lem1037603) (@lem1037602 d)). Qed.
Lemma lem1037605 : term212 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1037604 d)). Qed.
Lemma lem1037606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037679 : term107 = term258.
Proof. exact (MK_COMB (@lem1037606) (@lem1037605)). Qed.
Lemma lem1037680 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1037679) (@lem1037482 h1)). Qed.
Lemma lem1037828 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term535 w d' d z.
Proof. exact (EQ_MP (@lem1037511 w d' d z) (@lem1037479 w d' d z h1)). Qed.
Lemma lem1037861 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1037862 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1037861 n m)). Qed.
Lemma lem1037863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037864 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1037863) (@lem1037862 m)). Qed.
Lemma lem1037865 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1037864 m)). Qed.
Lemma lem1037866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037867 : term216 = term216.
Proof. exact (MK_COMB (@lem1037866) (@lem1037865)). Qed.
Lemma lem1037868 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1037867) (@lem1037552 h1)). Qed.
Lemma lem1037995 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term246 d e w x y z).
Proof. exact (eq_refl (term246 d e w x y z)). Qed.
Lemma lem1037996 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1037995 d e w x y z)). Qed.
Lemma lem1037997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1037998 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1037997) (@lem1037996 d e w x y)). Qed.
Lemma lem1037999 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1037998 d e w x y)). Qed.
Lemma lem1038000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038001 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1038000) (@lem1037999 d e w x)). Qed.
Lemma lem1038002 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1038001 d e w x)). Qed.
Lemma lem1038003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038004 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1038003) (@lem1038002 d e w)). Qed.
Lemma lem1038005 (d : nat) (e : nat) : (term253 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1038004 d e w)). Qed.
Lemma lem1038006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038007 (d : nat) (e : nat) : (term254 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1038006) (@lem1038005 d e)). Qed.
Lemma lem1038008 (d : nat) : (term255 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1038007 d e)). Qed.
Lemma lem1038009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038010 (d : nat) : (term256 d) = (term256 d).
Proof. exact (MK_COMB (@lem1038009) (@lem1038008 d)). Qed.
Lemma lem1038011 : term257 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1038010 d)). Qed.
Lemma lem1038012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038013 : term258 = term258.
Proof. exact (MK_COMB (@lem1038012) (@lem1038011)). Qed.
Lemma lem1038014 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1038013) (@lem1037680 h1)). Qed.
Lemma lem1038015 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term531 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1038016 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term528 w d' d z.
Proof. exact (h1). Qed.
Lemma lem1038017 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term527 w d' d z.
Proof. exact (proj2 (@lem1038015 w d' d z h1)). Qed.
Lemma lem1038021 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term162 w d' d z.
Proof. exact (proj2 (@lem1038016 w d' d z h1)). Qed.
Lemma lem1038036 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1038037 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1038036 n m)). Qed.
Lemma lem1038038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038039 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1038038) (@lem1038037 m)). Qed.
Lemma lem1038040 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1038039 m)). Qed.
Lemma lem1038041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038043 : term216 = term216.
Proof. exact (MK_COMB (@lem1038041) (@lem1038040)). Qed.
Lemma lem1038044 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1038043) (@lem1037868 h1)). Qed.
Lemma lem1038058 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1038075 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1038076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038077 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1038076) (@lem1038075 w x y z)). Qed.
Lemma lem1038078 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1038077 w x y z) (@lem1038058 w x y z)). Qed.
Lemma lem1038087 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1038088 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1038087 w x d y z e) (@lem1038078 w x y z)). Qed.
Lemma lem1038089 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1038090 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1038097 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1038098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038099 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1038098) (@lem1038097 d e w x y z)). Qed.
Lemma lem1038100 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1038099 d e w x y z) (@lem1038090 d e w x y z)). Qed.
Lemma lem1038101 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038089 d e w x y z) (@lem1038100 d e w x y z)). Qed.
Lemma lem1038102 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038088 d e w x y z) (@lem1038101 d e w x y z)). Qed.
Lemma lem1038103 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1038102 d e w x y z)). Qed.
Lemma lem1038104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038105 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1038104) (@lem1038103 d e w x y)). Qed.
Lemma lem1038106 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1038105 d e w x y)). Qed.
Lemma lem1038107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038108 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1038107) (@lem1038106 d e w x)). Qed.
Lemma lem1038109 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1038108 d e w x)). Qed.
Lemma lem1038110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038111 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1038110) (@lem1038109 d e w)). Qed.
Lemma lem1038112 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1038111 d e w)). Qed.
Lemma lem1038113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038114 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1038113) (@lem1038112 d e)). Qed.
Lemma lem1038115 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1038114 d e)). Qed.
Lemma lem1038116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038117 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1038116) (@lem1038115 d)). Qed.
Lemma lem1038118 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1038117 d)). Qed.
Lemma lem1038119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038121 : term258 = term284.
Proof. exact (MK_COMB (@lem1038119) (@lem1038118)). Qed.
Lemma lem1038122 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1038121) (@lem1038014 h1)). Qed.
Lemma lem1038146 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1038147 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1038146 n m)). Qed.
Lemma lem1038148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038149 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1038148) (@lem1038147 m)). Qed.
Lemma lem1038150 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1038149 m)). Qed.
Lemma lem1038151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038153 : term216 = term216.
Proof. exact (MK_COMB (@lem1038151) (@lem1038150)). Qed.
Lemma lem1038154 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1038153) (@lem1037868 h1)). Qed.
Lemma lem1038168 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1038185 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1038186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038187 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1038186) (@lem1038185 w x y z)). Qed.
Lemma lem1038188 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1038187 w x y z) (@lem1038168 w x y z)). Qed.
Lemma lem1038197 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1038198 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1038197 w x d y z e) (@lem1038188 w x y z)). Qed.
Lemma lem1038199 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1038200 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1038207 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1038208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038209 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1038208) (@lem1038207 d e w x y z)). Qed.
Lemma lem1038210 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1038209 d e w x y z) (@lem1038200 d e w x y z)). Qed.
Lemma lem1038211 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038199 d e w x y z) (@lem1038210 d e w x y z)). Qed.
Lemma lem1038212 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038198 d e w x y z) (@lem1038211 d e w x y z)). Qed.
Lemma lem1038213 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1038212 d e w x y z)). Qed.
Lemma lem1038214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038215 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1038214) (@lem1038213 d e w x y)). Qed.
Lemma lem1038216 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1038215 d e w x y)). Qed.
Lemma lem1038217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038218 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1038217) (@lem1038216 d e w x)). Qed.
Lemma lem1038219 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1038218 d e w x)). Qed.
Lemma lem1038220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038221 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1038220) (@lem1038219 d e w)). Qed.
Lemma lem1038222 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1038221 d e w)). Qed.
Lemma lem1038223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038224 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1038223) (@lem1038222 d e)). Qed.
Lemma lem1038225 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1038224 d e)). Qed.
Lemma lem1038226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038227 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1038226) (@lem1038225 d)). Qed.
Lemma lem1038228 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1038227 d)). Qed.
Lemma lem1038229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038231 : term258 = term284.
Proof. exact (MK_COMB (@lem1038229) (@lem1038228)). Qed.
Lemma lem1038232 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1038231) (@lem1038014 h1)). Qed.
Lemma lem1038240 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1038252 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1038253 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1038252 n m)). Qed.
Lemma lem1038254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038255 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1038254) (@lem1038253 m)). Qed.
Lemma lem1038256 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1038255 m)). Qed.
Lemma lem1038257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038259 : term216 = term216.
Proof. exact (MK_COMB (@lem1038257) (@lem1038256)). Qed.
Lemma lem1038260 (h1 : term216) : term216.
Proof. exact (EQ_MP (@lem1038259) (@lem1037868 h1)). Qed.
Lemma lem1038274 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1038291 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1038292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038293 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1038292) (@lem1038291 w x y z)). Qed.
Lemma lem1038294 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1038293 w x y z) (@lem1038274 w x y z)). Qed.
Lemma lem1038303 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1038304 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1038303 w x d y z e) (@lem1038294 w x y z)). Qed.
Lemma lem1038305 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1038306 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1038313 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1038314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038315 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1038314) (@lem1038313 d e w x y z)). Qed.
Lemma lem1038316 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1038315 d e w x y z) (@lem1038306 d e w x y z)). Qed.
Lemma lem1038317 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038305 d e w x y z) (@lem1038316 d e w x y z)). Qed.
Lemma lem1038318 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1038304 d e w x y z) (@lem1038317 d e w x y z)). Qed.
Lemma lem1038319 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1038318 d e w x y z)). Qed.
Lemma lem1038320 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038321 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1038320) (@lem1038319 d e w x y)). Qed.
Lemma lem1038322 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1038321 d e w x y)). Qed.
Lemma lem1038323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038324 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1038323) (@lem1038322 d e w x)). Qed.
Lemma lem1038325 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1038324 d e w x)). Qed.
Lemma lem1038326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038327 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1038326) (@lem1038325 d e w)). Qed.
Lemma lem1038328 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1038327 d e w)). Qed.
Lemma lem1038329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038330 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1038329) (@lem1038328 d e)). Qed.
Lemma lem1038331 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1038330 d e)). Qed.
Lemma lem1038332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038333 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1038332) (@lem1038331 d)). Qed.
Lemma lem1038334 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1038333 d)). Qed.
Lemma lem1038335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1038337 : term258 = term284.
Proof. exact (MK_COMB (@lem1038335) (@lem1038334)). Qed.
Lemma lem1038338 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1038337) (@lem1038014 h1)). Qed.
Lemma lem1038346 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1038353 (_17160 : nat) (h1 : term216) : term285 _17160.
Proof. exact (@lem1038044 h1 _17160). Qed.
Lemma lem1038354 (_17160 : nat) : (term285 _17160) = (term214 _17160).
Proof. exact (eq_refl (term285 _17160)). Qed.
Lemma lem1038355 (_17160 : nat) (h1 : term216) : term214 _17160.
Proof. exact (EQ_MP (@lem1038354 _17160) (@lem1038353 _17160 h1)). Qed.
Lemma lem1038356 (_17160 : nat) (_17161 : nat) (h1 : term216) : term286 _17160 _17161.
Proof. exact (@lem1038355 _17160 h1 _17161). Qed.
Lemma lem1038357 (_17161 : nat) (_17160 : nat) : (term286 _17160 _17161) = ((Nat.add _17160 _17161) = (Nat.add _17161 _17160)).
Proof. exact (eq_refl (term286 _17160 _17161)). Qed.
Lemma lem1038359 (_17162 : nat) (h1 : term107) : term287 _17162.
Proof. exact (@lem1038122 h1 _17162). Qed.
Lemma lem1038360 (_17162 : nat) : (term287 _17162) = (term282 _17162).
Proof. exact (eq_refl (term287 _17162)). Qed.
Lemma lem1038361 (_17162 : nat) (h1 : term107) : term282 _17162.
Proof. exact (EQ_MP (@lem1038360 _17162) (@lem1038359 _17162 h1)). Qed.
Lemma lem1038362 (_17162 : nat) (_17163 : nat) (h1 : term107) : term288 _17162 _17163.
Proof. exact (@lem1038361 _17162 h1 _17163). Qed.
Lemma lem1038363 (_17162 : nat) (_17163 : nat) : (term288 _17162 _17163) = (term280 _17162 _17163).
Proof. exact (eq_refl (term288 _17162 _17163)). Qed.
Lemma lem1038364 (_17162 : nat) (_17163 : nat) (h1 : term107) : term280 _17162 _17163.
Proof. exact (EQ_MP (@lem1038363 _17162 _17163) (@lem1038362 _17162 _17163 h1)). Qed.
Lemma lem1038365 (_17162 : nat) (_17163 : nat) (_17164 : nat) (h1 : term107) : term289 _17162 _17163 _17164.
Proof. exact (@lem1038364 _17162 _17163 h1 _17164). Qed.
Lemma lem1038366 (_17162 : nat) (_17163 : nat) (_17164 : nat) : (term289 _17162 _17163 _17164) = (term278 _17162 _17163 _17164).
Proof. exact (eq_refl (term289 _17162 _17163 _17164)). Qed.
Lemma lem1038367 (_17162 : nat) (_17163 : nat) (_17164 : nat) (h1 : term107) : term278 _17162 _17163 _17164.
Proof. exact (EQ_MP (@lem1038366 _17162 _17163 _17164) (@lem1038365 _17162 _17163 _17164 h1)). Qed.
Lemma lem1038368 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (h1 : term107) : term290 _17162 _17163 _17164 _17165.
Proof. exact (@lem1038367 _17162 _17163 _17164 h1 _17165). Qed.
Lemma lem1038369 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) : (term290 _17162 _17163 _17164 _17165) = (term276 _17162 _17163 _17164 _17165).
Proof. exact (eq_refl (term290 _17162 _17163 _17164 _17165)). Qed.
Lemma lem1038370 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (h1 : term107) : term276 _17162 _17163 _17164 _17165.
Proof. exact (EQ_MP (@lem1038369 _17162 _17163 _17164 _17165) (@lem1038368 _17162 _17163 _17164 _17165 h1)). Qed.
Lemma lem1038371 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (h1 : term107) : term291 _17162 _17163 _17164 _17165 _17166.
Proof. exact (@lem1038370 _17162 _17163 _17164 _17165 h1 _17166). Qed.
Lemma lem1038372 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) : (term291 _17162 _17163 _17164 _17165 _17166) = (term274 _17162 _17163 _17164 _17165 _17166).
Proof. exact (eq_refl (term291 _17162 _17163 _17164 _17165 _17166)). Qed.
Lemma lem1038373 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (h1 : term107) : term274 _17162 _17163 _17164 _17165 _17166.
Proof. exact (EQ_MP (@lem1038372 _17162 _17163 _17164 _17165 _17166) (@lem1038371 _17162 _17163 _17164 _17165 _17166 h1)). Qed.
Lemma lem1038374 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) (h1 : term107) : term292 _17162 _17163 _17164 _17165 _17166 _17167.
Proof. exact (@lem1038373 _17162 _17163 _17164 _17165 _17166 h1 _17167). Qed.
Lemma lem1038375 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term292 _17162 _17163 _17164 _17165 _17166 _17167) = (term272 _17162 _17163 _17164 _17165 _17166 _17167).
Proof. exact (eq_refl (term292 _17162 _17163 _17164 _17165 _17166 _17167)). Qed.
Lemma lem1038376 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) (h1 : term107) : term272 _17162 _17163 _17164 _17165 _17166 _17167.
Proof. exact (EQ_MP (@lem1038375 _17162 _17163 _17164 _17165 _17166 _17167) (@lem1038374 _17162 _17163 _17164 _17165 _17166 _17167 h1)). Qed.
Lemma lem1038383 (_17170 : nat) (h1 : term216) : term285 _17170.
Proof. exact (@lem1038154 h1 _17170). Qed.
Lemma lem1038384 (_17170 : nat) : (term285 _17170) = (term214 _17170).
Proof. exact (eq_refl (term285 _17170)). Qed.
Lemma lem1038385 (_17170 : nat) (h1 : term216) : term214 _17170.
Proof. exact (EQ_MP (@lem1038384 _17170) (@lem1038383 _17170 h1)). Qed.
Lemma lem1038386 (_17170 : nat) (_17171 : nat) (h1 : term216) : term286 _17170 _17171.
Proof. exact (@lem1038385 _17170 h1 _17171). Qed.
Lemma lem1038387 (_17171 : nat) (_17170 : nat) : (term286 _17170 _17171) = ((Nat.add _17170 _17171) = (Nat.add _17171 _17170)).
Proof. exact (eq_refl (term286 _17170 _17171)). Qed.
Lemma lem1038389 (_17172 : nat) (h1 : term107) : term287 _17172.
Proof. exact (@lem1038232 h1 _17172). Qed.
Lemma lem1038390 (_17172 : nat) : (term287 _17172) = (term282 _17172).
Proof. exact (eq_refl (term287 _17172)). Qed.
Lemma lem1038391 (_17172 : nat) (h1 : term107) : term282 _17172.
Proof. exact (EQ_MP (@lem1038390 _17172) (@lem1038389 _17172 h1)). Qed.
Lemma lem1038392 (_17172 : nat) (_17173 : nat) (h1 : term107) : term288 _17172 _17173.
Proof. exact (@lem1038391 _17172 h1 _17173). Qed.
Lemma lem1038393 (_17172 : nat) (_17173 : nat) : (term288 _17172 _17173) = (term280 _17172 _17173).
Proof. exact (eq_refl (term288 _17172 _17173)). Qed.
Lemma lem1038394 (_17172 : nat) (_17173 : nat) (h1 : term107) : term280 _17172 _17173.
Proof. exact (EQ_MP (@lem1038393 _17172 _17173) (@lem1038392 _17172 _17173 h1)). Qed.
Lemma lem1038395 (_17172 : nat) (_17173 : nat) (_17174 : nat) (h1 : term107) : term289 _17172 _17173 _17174.
Proof. exact (@lem1038394 _17172 _17173 h1 _17174). Qed.
Lemma lem1038396 (_17172 : nat) (_17173 : nat) (_17174 : nat) : (term289 _17172 _17173 _17174) = (term278 _17172 _17173 _17174).
Proof. exact (eq_refl (term289 _17172 _17173 _17174)). Qed.
Lemma lem1038397 (_17172 : nat) (_17173 : nat) (_17174 : nat) (h1 : term107) : term278 _17172 _17173 _17174.
Proof. exact (EQ_MP (@lem1038396 _17172 _17173 _17174) (@lem1038395 _17172 _17173 _17174 h1)). Qed.
Lemma lem1038398 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (h1 : term107) : term290 _17172 _17173 _17174 _17175.
Proof. exact (@lem1038397 _17172 _17173 _17174 h1 _17175). Qed.
Lemma lem1038399 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term290 _17172 _17173 _17174 _17175) = (term276 _17172 _17173 _17174 _17175).
Proof. exact (eq_refl (term290 _17172 _17173 _17174 _17175)). Qed.
Lemma lem1038400 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (h1 : term107) : term276 _17172 _17173 _17174 _17175.
Proof. exact (EQ_MP (@lem1038399 _17172 _17173 _17174 _17175) (@lem1038398 _17172 _17173 _17174 _17175 h1)). Qed.
Lemma lem1038401 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (h1 : term107) : term291 _17172 _17173 _17174 _17175 _17176.
Proof. exact (@lem1038400 _17172 _17173 _17174 _17175 h1 _17176). Qed.
Lemma lem1038402 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) : (term291 _17172 _17173 _17174 _17175 _17176) = (term274 _17172 _17173 _17174 _17175 _17176).
Proof. exact (eq_refl (term291 _17172 _17173 _17174 _17175 _17176)). Qed.
Lemma lem1038403 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (h1 : term107) : term274 _17172 _17173 _17174 _17175 _17176.
Proof. exact (EQ_MP (@lem1038402 _17172 _17173 _17174 _17175 _17176) (@lem1038401 _17172 _17173 _17174 _17175 _17176 h1)). Qed.
Lemma lem1038404 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (h1 : term107) : term292 _17172 _17173 _17174 _17175 _17176 _17177.
Proof. exact (@lem1038403 _17172 _17173 _17174 _17175 _17176 h1 _17177). Qed.
Lemma lem1038405 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) : (term292 _17172 _17173 _17174 _17175 _17176 _17177) = (term272 _17172 _17173 _17174 _17175 _17176 _17177).
Proof. exact (eq_refl (term292 _17172 _17173 _17174 _17175 _17176 _17177)). Qed.
Lemma lem1038406 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (h1 : term107) : term272 _17172 _17173 _17174 _17175 _17176 _17177.
Proof. exact (EQ_MP (@lem1038405 _17172 _17173 _17174 _17175 _17176 _17177) (@lem1038404 _17172 _17173 _17174 _17175 _17176 _17177 h1)). Qed.
Lemma lem1038413 (_17180 : nat) (h1 : term216) : term285 _17180.
Proof. exact (@lem1038260 h1 _17180). Qed.
Lemma lem1038414 (_17180 : nat) : (term285 _17180) = (term214 _17180).
Proof. exact (eq_refl (term285 _17180)). Qed.
Lemma lem1038415 (_17180 : nat) (h1 : term216) : term214 _17180.
Proof. exact (EQ_MP (@lem1038414 _17180) (@lem1038413 _17180 h1)). Qed.
Lemma lem1038416 (_17180 : nat) (_17181 : nat) (h1 : term216) : term286 _17180 _17181.
Proof. exact (@lem1038415 _17180 h1 _17181). Qed.
Lemma lem1038417 (_17181 : nat) (_17180 : nat) : (term286 _17180 _17181) = ((Nat.add _17180 _17181) = (Nat.add _17181 _17180)).
Proof. exact (eq_refl (term286 _17180 _17181)). Qed.
Lemma lem1038419 (_17182 : nat) (h1 : term107) : term287 _17182.
Proof. exact (@lem1038338 h1 _17182). Qed.
Lemma lem1038420 (_17182 : nat) : (term287 _17182) = (term282 _17182).
Proof. exact (eq_refl (term287 _17182)). Qed.
Lemma lem1038421 (_17182 : nat) (h1 : term107) : term282 _17182.
Proof. exact (EQ_MP (@lem1038420 _17182) (@lem1038419 _17182 h1)). Qed.
Lemma lem1038422 (_17182 : nat) (_17183 : nat) (h1 : term107) : term288 _17182 _17183.
Proof. exact (@lem1038421 _17182 h1 _17183). Qed.
Lemma lem1038423 (_17182 : nat) (_17183 : nat) : (term288 _17182 _17183) = (term280 _17182 _17183).
Proof. exact (eq_refl (term288 _17182 _17183)). Qed.
Lemma lem1038424 (_17182 : nat) (_17183 : nat) (h1 : term107) : term280 _17182 _17183.
Proof. exact (EQ_MP (@lem1038423 _17182 _17183) (@lem1038422 _17182 _17183 h1)). Qed.
Lemma lem1038425 (_17182 : nat) (_17183 : nat) (_17184 : nat) (h1 : term107) : term289 _17182 _17183 _17184.
Proof. exact (@lem1038424 _17182 _17183 h1 _17184). Qed.
Lemma lem1038426 (_17182 : nat) (_17183 : nat) (_17184 : nat) : (term289 _17182 _17183 _17184) = (term278 _17182 _17183 _17184).
Proof. exact (eq_refl (term289 _17182 _17183 _17184)). Qed.
Lemma lem1038427 (_17182 : nat) (_17183 : nat) (_17184 : nat) (h1 : term107) : term278 _17182 _17183 _17184.
Proof. exact (EQ_MP (@lem1038426 _17182 _17183 _17184) (@lem1038425 _17182 _17183 _17184 h1)). Qed.
Lemma lem1038428 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (h1 : term107) : term290 _17182 _17183 _17184 _17185.
Proof. exact (@lem1038427 _17182 _17183 _17184 h1 _17185). Qed.
Lemma lem1038429 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) : (term290 _17182 _17183 _17184 _17185) = (term276 _17182 _17183 _17184 _17185).
Proof. exact (eq_refl (term290 _17182 _17183 _17184 _17185)). Qed.
Lemma lem1038430 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (h1 : term107) : term276 _17182 _17183 _17184 _17185.
Proof. exact (EQ_MP (@lem1038429 _17182 _17183 _17184 _17185) (@lem1038428 _17182 _17183 _17184 _17185 h1)). Qed.
Lemma lem1038431 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (h1 : term107) : term291 _17182 _17183 _17184 _17185 _17186.
Proof. exact (@lem1038430 _17182 _17183 _17184 _17185 h1 _17186). Qed.
Lemma lem1038432 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) : (term291 _17182 _17183 _17184 _17185 _17186) = (term274 _17182 _17183 _17184 _17185 _17186).
Proof. exact (eq_refl (term291 _17182 _17183 _17184 _17185 _17186)). Qed.
Lemma lem1038433 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (h1 : term107) : term274 _17182 _17183 _17184 _17185 _17186.
Proof. exact (EQ_MP (@lem1038432 _17182 _17183 _17184 _17185 _17186) (@lem1038431 _17182 _17183 _17184 _17185 _17186 h1)). Qed.
Lemma lem1038434 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term292 _17182 _17183 _17184 _17185 _17186 _17187.
Proof. exact (@lem1038433 _17182 _17183 _17184 _17185 _17186 h1 _17187). Qed.
Lemma lem1038435 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) : (term292 _17182 _17183 _17184 _17185 _17186 _17187) = (term272 _17182 _17183 _17184 _17185 _17186 _17187).
Proof. exact (eq_refl (term292 _17182 _17183 _17184 _17185 _17186 _17187)). Qed.
Lemma lem1038436 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term272 _17182 _17183 _17184 _17185 _17186 _17187.
Proof. exact (EQ_MP (@lem1038435 _17182 _17183 _17184 _17185 _17186 _17187) (@lem1038434 _17182 _17183 _17184 _17185 _17186 _17187 h1)). Qed.
Lemma lem1038437 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) (h1 : term107) : term265 _17162 _17163 _17164 _17165 _17166 _17167.
Proof. exact (proj2 (@lem1038376 _17162 _17163 _17164 _17165 _17166 _17167 h1)). Qed.
Lemma lem1038442 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (h1 : term107) : term267 _17172 _17173 _17174 _17175 _17176 _17177.
Proof. exact (proj1 (@lem1038406 _17172 _17173 _17174 _17175 _17176 _17177 h1)). Qed.
Lemma lem1038444 (_17172 : nat) (_17173 : nat) (_17177 : nat) (_17176 : nat) (_17174 : nat) (_17175 : nat) (h1 : term107) : term293 _17172 _17173 _17177 _17176 _17174 _17175.
Proof. exact (proj1 (@lem1038442 _17172 _17173 _17174 _17175 _17176 _17177 h1)). Qed.
Lemma lem1038446 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term267 _17182 _17183 _17184 _17185 _17186 _17187.
Proof. exact (proj1 (@lem1038436 _17182 _17183 _17184 _17185 _17186 _17187 h1)). Qed.
Lemma lem1038447 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term536 _17182 _17183 _17184 _17185 _17186 _17187.
Proof. exact (proj2 (@lem1038446 _17182 _17183 _17184 _17185 _17186 _17187 h1)). Qed.
Lemma lem1038458 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term349 d z.
Proof. exact (proj2 (@lem1038017 w d' d z h1)). Qed.
Lemma lem1038477 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term265 _17162 _17163 _17164 _17165 _17166 _17167) = (term295 _17162 _17163 _17164 _17165 _17166 _17167).
Proof. exact (@lem1033471 (term296 _17164 _17165 _17162) (term296 _17166 _17167 _17163) (term235 _17164 _17165 _17166 _17167)). Qed.
Lemma lem1038478 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) (h1 : term107) : term295 _17162 _17163 _17164 _17165 _17166 _17167.
Proof. exact (EQ_MP (@lem1038477 _17162 _17163 _17164 _17165 _17166 _17167) (@lem1038437 _17162 _17163 _17164 _17165 _17166 _17167 h1)). Qed.
Lemma lem1038516 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term537 w d' z d.
Proof. exact (proj1 (@lem1038016 w d' d z h1)). Qed.
Lemma lem1038518 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1038553 (_17172 : nat) (_17173 : nat) (_17177 : nat) (_17176 : nat) (_17174 : nat) (_17175 : nat) : (term293 _17172 _17173 _17177 _17176 _17174 _17175) = (term298 _17172 _17173 _17177 _17176 _17174 _17175).
Proof. exact (@lem1033471 (term296 _17174 _17175 _17172) (term296 _17176 _17177 _17173) (term268 _17177 _17176 _17174 _17175)). Qed.
Lemma lem1038554 (_17172 : nat) (_17173 : nat) (_17177 : nat) (_17176 : nat) (_17174 : nat) (_17175 : nat) (h1 : term107) : term298 _17172 _17173 _17177 _17176 _17174 _17175.
Proof. exact (EQ_MP (@lem1038553 _17172 _17173 _17177 _17176 _17174 _17175) (@lem1038444 _17172 _17173 _17177 _17176 _17174 _17175 h1)). Qed.
Lemma lem1038576 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term537 w d' z d.
Proof. exact (proj1 (@lem1038016 w d' d z h1)). Qed.
Lemma lem1038578 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1038629 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) : (term536 _17182 _17183 _17184 _17185 _17186 _17187) = (term538 _17182 _17183 _17184 _17185 _17186 _17187).
Proof. exact (@lem1033471 (term296 _17184 _17185 _17182) (term296 _17186 _17187 _17183) (term269 _17184 _17185 _17186 _17187)). Qed.
Lemma lem1038630 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term538 _17182 _17183 _17184 _17185 _17186 _17187.
Proof. exact (EQ_MP (@lem1038629 _17182 _17183 _17184 _17185 _17186 _17187) (@lem1038447 _17182 _17183 _17184 _17185 _17186 _17187 h1)). Qed.
Lemma lem1038662 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1038664 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1038665 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1038664 (Nat.add w d')). Qed.
Lemma lem1038666 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1038665 w d'). Qed.
Lemma lem1038668 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038669 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1038668 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1038670 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1038669 w d') (@lem1038666 w d')). Qed.
Lemma lem1038672 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1038673 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1038672 (Nat.add z d)). Qed.
Lemma lem1038674 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1038673 z d). Qed.
Lemma lem1038676 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038677 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1038676 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1038678 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1038677 z d) (@lem1038674 z d)). Qed.
Lemma lem1038680 (_17161 : nat) (_17160 : nat) (h1 : term216) : (Nat.add _17160 _17161) = (Nat.add _17161 _17160).
Proof. exact (EQ_MP (@lem1038357 _17161 _17160) (@lem1038356 _17160 _17161 h1)). Qed.
Lemma lem1038681 (d' : nat) (d : nat) (w : nat) (z : nat) (h1 : term216) : (term149 w d' z d) = (term54 d' d w z).
Proof. exact (@lem1038680 (term50 w d' z d) (Nat.mul w z) h1). Qed.
Lemma lem1038682 (d' : nat) (d : nat) (w : nat) (z : nat) (h1 : term216) : term304 d' d w z.
Proof. exact (fun h0 : term305 d' d w z => @lem1038681 d' d w z h1). Qed.
Lemma lem1038684 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038685 (d' : nat) (d : nat) (w : nat) (z : nat) : (term304 d' d w z) = ((term149 w d' z d) = (term54 d' d w z)).
Proof. exact (@lem1038684 ((term149 w d' z d) = (term54 d' d w z))). Qed.
Lemma lem1038686 (d' : nat) (d : nat) (w : nat) (z : nat) (h1 : term216) : (term149 w d' z d) = (term54 d' d w z).
Proof. exact (EQ_MP (@lem1038685 d' d w z) (@lem1038682 d' d w z h1)). Qed.
Lemma lem1038688 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (proj1 (@lem1038015 w d' d z h1)). Qed.
Lemma lem1038689 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term539 w d' z d.
Proof. exact (fun h0 : term537 w d' z d => @lem1038688 w d' d z h1). Qed.
Lemma lem1038691 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038692 (w : nat) (d' : nat) (z : nat) (d : nat) : (term539 w d' z d) = ((term150 d w d' z) = (term149 w d' z d)).
Proof. exact (@lem1038691 ((term150 d w d' z) = (term149 w d' z d))). Qed.
Lemma lem1038693 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1038692 w d' z d) (@lem1038689 w d' d z h1)). Qed.
Lemma lem1038695 (_17161 : nat) (_17160 : nat) (h1 : term216) : (Nat.add _17160 _17161) = (Nat.add _17161 _17160).
Proof. exact (EQ_MP (@lem1038357 _17161 _17160) (@lem1038356 _17160 _17161 h1)). Qed.
Lemma lem1038696 (d' : nat) (w : nat) (z : nat) (d : nat) (h1 : term216) : (term150 d w d' z) = (term58 d' w z d).
Proof. exact (@lem1038695 (term39 w d' z) (term46 w z d) h1). Qed.
Lemma lem1038697 (d' : nat) (w : nat) (z : nat) (d : nat) (h1 : term216) : term332 d' w z d.
Proof. exact (fun h0 : term333 d' w z d => @lem1038696 d' w z d h1). Qed.
Lemma lem1038699 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038700 (d' : nat) (w : nat) (z : nat) (d : nat) : (term332 d' w z d) = ((term150 d w d' z) = (term58 d' w z d)).
Proof. exact (@lem1038699 ((term150 d w d' z) = (term58 d' w z d))). Qed.
Lemma lem1038701 (d' : nat) (w : nat) (z : nat) (d : nat) (h1 : term216) : (term150 d w d' z) = (term58 d' w z d).
Proof. exact (EQ_MP (@lem1038700 d' w z d) (@lem1038697 d' w z d h1)). Qed.
Lemma lem1038719 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1038720 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1038719 (y = z) (term260 x z)). Qed.
Lemma lem1038730 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1038731 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1038730 x y) (@lem1038720 y x z)). Qed.
Lemma lem1038735 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1038736 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1038735 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1038758 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1038731 y x z) (@lem1038736 y x z)). Qed.
Lemma lem1038759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1038760 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1038759) (@lem1038758 y x z)). Qed.
Lemma lem1038782 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1038783 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1038760 y x z) (@lem1038782 y x z)). Qed.
Lemma lem1038785 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1038786 (x : Prop) : (x = x) = True.
Proof. exact (@lem1038785 Prop x). Qed.
Lemma lem1038787 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1038786 (term310 y x z)). Qed.
Lemma lem1038788 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1038783 y x z) (@lem1038787 y x z)). Qed.
Lemma lem1038789 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1038788 y x z)). Qed.
Lemma lem1038790 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1038789 y x z) (@lem0)). Qed.
Lemma lem1038791 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1038790 y x z) (@lem1038662 x y z)). Qed.
Lemma lem1038793 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1038794 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1038793 (term315 y x z) (y = z)). Qed.
Lemma lem1038796 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1038797 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1038796 (term260 x y) (term260 x z)). Qed.
Lemma lem1038799 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1038800 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1038799 (x = y)). Qed.
Lemma lem1038801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038802 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1038801) (@lem1038800 x y)). Qed.
Lemma lem1038804 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1038805 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1038804 (x = z)). Qed.
Lemma lem1038806 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1038802 x y) (@lem1038805 x z)). Qed.
Lemma lem1038807 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1038797 y x z) (@lem1038806 y x z)). Qed.
Lemma lem1038808 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1038809 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1038808) (@lem1038807 y x z)). Qed.
Lemma lem1038810 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1038811 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1038809 y x z) (@lem1038810 y z)). Qed.
Lemma lem1038812 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1038794 x y z) (@lem1038811 x y z)). Qed.
Lemma lem1038814 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term540 d' w z d.
Proof. exact (conj (@lem1038693 w d' d z h2) (@lem1038701 d' w z d h1)). Qed.
Lemma lem1038816 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1038812 x y z) (@lem1038791 y x z)). Qed.
Lemma lem1038817 (d' : nat) (w : nat) (z : nat) (d : nat) : term541 d' w z d.
Proof. exact (@lem1038816 (term150 d w d' z) (term149 w d' z d) (term58 d' w z d)). Qed.
Lemma lem1038820 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : (term149 w d' z d) = (term58 d' w z d).
Proof. exact (@lem1038817 d' w z d (@lem1038814 w d' d z h1 h2)). Qed.
Lemma lem1038821 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term542 d' w z d.
Proof. exact (fun h0 : term543 d' w z d => @lem1038820 w d' d z h1 h2). Qed.
Lemma lem1038823 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038824 (d' : nat) (w : nat) (z : nat) (d : nat) : (term542 d' w z d) = ((term149 w d' z d) = (term58 d' w z d)).
Proof. exact (@lem1038823 ((term149 w d' z d) = (term58 d' w z d))). Qed.
Lemma lem1038825 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : (term149 w d' z d) = (term58 d' w z d).
Proof. exact (EQ_MP (@lem1038824 d' w z d) (@lem1038821 w d' d z h1 h2)). Qed.
Lemma lem1038826 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term544 d' w z d.
Proof. exact (conj (@lem1038686 d' d w z h1) (@lem1038825 w d' d z h1 h2)). Qed.
Lemma lem1038828 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1038812 x y z) (@lem1038791 y x z)). Qed.
Lemma lem1038829 (d' : nat) (w : nat) (z : nat) (d : nat) : term545 d' w z d.
Proof. exact (@lem1038828 (term149 w d' z d) (term54 d' d w z) (term58 d' w z d)). Qed.
Lemma lem1038832 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (@lem1038829 d' w z d (@lem1038826 w d' d z h1 h2)). Qed.
Lemma lem1038833 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term336 d' w z d.
Proof. exact (fun h0 : term337 d' w z d => @lem1038832 w d' d z h1 h2). Qed.
Lemma lem1038835 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038836 (d' : nat) (w : nat) (z : nat) (d : nat) : (term336 d' w z d) = ((term54 d' d w z) = (term58 d' w z d)).
Proof. exact (@lem1038835 ((term54 d' d w z) = (term58 d' w z d))). Qed.
Lemma lem1038837 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (EQ_MP (@lem1038836 d' w z d) (@lem1038833 w d' d z h1 h2)). Qed.
Lemma lem1038839 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1038840 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1038839 (Nat.add w d')). Qed.
Lemma lem1038841 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1038840 w d'). Qed.
Lemma lem1038843 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1038844 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1038843 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1038845 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1038844 w d') (@lem1038841 w d')). Qed.
Lemma lem1038847 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term294 w d'.
Proof. exact (proj1 (@lem1038017 w d' d z h1)). Qed.
Lemma lem1038848 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term338 w d'.
Proof. exact (fun h0 : w = (Nat.add w d') => @lem1038847 w d' d z h1). Qed.
Lemma lem1038850 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1038851 (w : nat) (d' : nat) : (term338 w d') = (term294 w d').
Proof. exact (@lem1038850 (w = (Nat.add w d'))). Qed.
Lemma lem1038852 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term294 w d'.
Proof. exact (EQ_MP (@lem1038851 w d') (@lem1038848 w d' d z h1)). Qed.
Lemma lem1038854 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1038855 (z : nat) (x : nat) (y : nat) : (term299 x y z) = (term340 z x y).
Proof. exact (@lem1038854 (term306 x y z) (term260 x y)). Qed.
Lemma lem1038857 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1038858 (x : nat) (y : nat) (z : nat) : (term341 x y z) = (term342 x y z).
Proof. exact (@lem1038857 (term260 x z) (y = z)). Qed.
Lemma lem1038860 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1038861 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1038860 (x = z)). Qed.
Lemma lem1038862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1038863 (x : nat) (z : nat) : (term322 x z) = (term323 x z).
Proof. exact (MK_COMB (@lem1038862) (@lem1038861 x z)). Qed.
Lemma lem1038864 (y : nat) (z : nat) : (term260 y z) = (term260 y z).
Proof. exact (eq_refl (term260 y z)). Qed.
Lemma lem1038865 (x : nat) (y : nat) (z : nat) : (term342 x y z) = (term343 x y z).
Proof. exact (MK_COMB (@lem1038863 x z) (@lem1038864 y z)). Qed.
Lemma lem1038866 (x : nat) (y : nat) (z : nat) : (term341 x y z) = (term343 x y z).
Proof. exact (TRANS (@lem1038858 x y z) (@lem1038865 x y z)). Qed.
Lemma lem1038867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1038868 (x : nat) (y : nat) (z : nat) : (term344 x y z) = (term345 x y z).
Proof. exact (MK_COMB (@lem1038867) (@lem1038866 x y z)). Qed.
Lemma lem1038869 (x : nat) (y : nat) : (term260 x y) = (term260 x y).
Proof. exact (eq_refl (term260 x y)). Qed.
Lemma lem1038870 (z : nat) (x : nat) (y : nat) : (term340 z x y) = (term346 z x y).
Proof. exact (MK_COMB (@lem1038868 x y z) (@lem1038869 x y)). Qed.
Lemma lem1038871 (z : nat) (x : nat) (y : nat) : (term299 x y z) = (term346 z x y).
Proof. exact (TRANS (@lem1038855 z x y) (@lem1038870 z x y)). Qed.
Lemma lem1038873 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term347 w d'.
Proof. exact (conj (@lem1038845 w d') (@lem1038852 w d' d z h1)). Qed.
Lemma lem1038875 (z : nat) (x : nat) (y : nat) : term346 z x y.
Proof. exact (EQ_MP (@lem1038871 z x y) (@lem1038662 x y z)). Qed.
Lemma lem1038876 (d' : nat) (w : nat) : term348 d' w.
Proof. exact (@lem1038875 (Nat.add w d') (Nat.add w d') w). Qed.
Lemma lem1038879 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term349 d' w.
Proof. exact (@lem1038876 d' w (@lem1038873 w d' d z h1)). Qed.
Lemma lem1038880 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term350 d' w.
Proof. exact (fun h0 : (Nat.add w d') = w => @lem1038879 w d' d z h1). Qed.
Lemma lem1038882 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1038883 (d' : nat) (w : nat) : (term350 d' w) = (term349 d' w).
Proof. exact (@lem1038882 ((Nat.add w d') = w)). Qed.
Lemma lem1038884 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term349 d' w.
Proof. exact (EQ_MP (@lem1038883 d' w) (@lem1038880 w d' d z h1)). Qed.
Lemma lem1038914 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1038915 (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term235 _17164 _17165 _17166 _17167) = (term351 _17164 _17165 _17166 _17167).
Proof. exact (@lem1038914 (_17164 = _17165) (term352 _17164 _17167 _17165 _17166) (_17166 = _17167)). Qed.
Lemma lem1038931 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1038932 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term353 _17164 _17165 _17166 _17167) = (term354 _17164 _17167 _17165 _17166).
Proof. exact (@lem1038931 (_17166 = _17167) (term352 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1038942 (_17164 : nat) (_17165 : nat) : (term62 _17164 _17165) = (term62 _17164 _17165).
Proof. exact (eq_refl (term62 _17164 _17165)). Qed.
Lemma lem1038943 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term351 _17164 _17165 _17166 _17167) = (term355 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1038942 _17164 _17165) (@lem1038932 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1038954 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term235 _17164 _17165 _17166 _17167) = (term355 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1038915 _17164 _17165 _17166 _17167) (@lem1038943 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1038955 (_17166 : nat) (_17167 : nat) (_17163 : nat) : (term356 _17166 _17167 _17163) = (term356 _17166 _17167 _17163).
Proof. exact (eq_refl (term356 _17166 _17167 _17163)). Qed.
Lemma lem1038956 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term357 _17163 _17164 _17165 _17166 _17167) = (term358 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1038955 _17166 _17167 _17163) (@lem1038954 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1038960 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1038961 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term358 _17163 _17164 _17167 _17165 _17166) = (term359 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1038960 (_17164 = _17165) (term296 _17166 _17167 _17163) (term354 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1038977 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1038978 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term360 _17163 _17164 _17167 _17165 _17166) = (term361 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1038977 (_17166 = _17167) (term296 _17166 _17167 _17163) (term352 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039000 (_17164 : nat) (_17165 : nat) : (term62 _17164 _17165) = (term62 _17164 _17165).
Proof. exact (eq_refl (term62 _17164 _17165)). Qed.
Lemma lem1039001 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term359 _17163 _17164 _17167 _17165 _17166) = (term362 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039000 _17164 _17165) (@lem1038978 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039012 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term358 _17163 _17164 _17167 _17165 _17166) = (term362 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1038961 _17163 _17164 _17167 _17165 _17166) (@lem1039001 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039013 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term357 _17163 _17164 _17165 _17166 _17167) = (term362 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1038956 _17163 _17164 _17167 _17165 _17166) (@lem1039012 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039014 (_17164 : nat) (_17165 : nat) (_17162 : nat) : (term356 _17164 _17165 _17162) = (term356 _17164 _17165 _17162).
Proof. exact (eq_refl (term356 _17164 _17165 _17162)). Qed.
Lemma lem1039015 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term363 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039014 _17164 _17165 _17162) (@lem1039013 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039019 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039020 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term363 _17162 _17163 _17164 _17167 _17165 _17166) = (term364 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039019 (_17164 = _17165) (term296 _17164 _17165 _17162) (term361 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039036 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039037 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term365 _17162 _17163 _17164 _17167 _17165 _17166) = (term366 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039036 (_17166 = _17167) (term296 _17164 _17165 _17162) (term367 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039071 (_17164 : nat) (_17165 : nat) : (term62 _17164 _17165) = (term62 _17164 _17165).
Proof. exact (eq_refl (term62 _17164 _17165)). Qed.
Lemma lem1039072 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term364 _17162 _17163 _17164 _17167 _17165 _17166) = (term368 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039071 _17164 _17165) (@lem1039037 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039083 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term363 _17162 _17163 _17164 _17167 _17165 _17166) = (term368 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1039020 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039072 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039084 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term368 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1039015 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039083 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1039086 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term369 _17162 _17163 _17164 _17165 _17166 _17167) = (term370 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039085) (@lem1039084 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039126 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1039127 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term371 _17167 _17166 _17164 _17165) = (term372 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039126 (_17164 = _17165) (term352 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039137 (_17166 : nat) (_17167 : nat) (_17163 : nat) : (term356 _17166 _17167 _17163) = (term356 _17166 _17167 _17163).
Proof. exact (eq_refl (term356 _17166 _17167 _17163)). Qed.
Lemma lem1039138 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term373 _17163 _17167 _17166 _17164 _17165) = (term374 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039137 _17166 _17167 _17163) (@lem1039127 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039142 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039143 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term374 _17163 _17164 _17167 _17165 _17166) = (term375 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039142 (_17164 = _17165) (term296 _17166 _17167 _17163) (term352 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039165 (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term373 _17163 _17167 _17166 _17164 _17165) = (term375 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1039138 _17163 _17164 _17167 _17165 _17166) (@lem1039143 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039166 (_17164 : nat) (_17165 : nat) (_17162 : nat) : (term356 _17164 _17165 _17162) = (term356 _17164 _17165 _17162).
Proof. exact (eq_refl (term356 _17164 _17165 _17162)). Qed.
Lemma lem1039167 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term376 _17162 _17163 _17167 _17166 _17164 _17165) = (term377 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039166 _17164 _17165 _17162) (@lem1039165 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039171 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039172 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term377 _17162 _17163 _17164 _17167 _17165 _17166) = (term378 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039171 (_17164 = _17165) (term296 _17164 _17165 _17162) (term367 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039206 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term376 _17162 _17163 _17167 _17166 _17164 _17165) = (term378 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1039167 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039172 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039207 (_17166 : nat) (_17167 : nat) : (term62 _17166 _17167) = (term62 _17166 _17167).
Proof. exact (eq_refl (term62 _17166 _17167)). Qed.
Lemma lem1039208 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term379 _17162 _17163 _17167 _17166 _17164 _17165) = (term380 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039207 _17166 _17167) (@lem1039206 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039212 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039213 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term380 _17162 _17163 _17164 _17167 _17165 _17166) = (term368 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (@lem1039212 (_17164 = _17165) (_17166 = _17167) (term381 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039259 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term379 _17162 _17163 _17167 _17166 _17164 _17165) = (term368 _17162 _17163 _17164 _17167 _17165 _17166).
Proof. exact (TRANS (@lem1039208 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039213 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039260 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : ((term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term379 _17162 _17163 _17167 _17166 _17164 _17165)) = ((term368 _17162 _17163 _17164 _17167 _17165 _17166) = (term368 _17162 _17163 _17164 _17167 _17165 _17166)).
Proof. exact (MK_COMB (@lem1039086 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039259 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039262 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1039263 (x : Prop) : (x = x) = True.
Proof. exact (@lem1039262 Prop x). Qed.
Lemma lem1039264 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : ((term368 _17162 _17163 _17164 _17167 _17165 _17166) = (term368 _17162 _17163 _17164 _17167 _17165 _17166)) = True.
Proof. exact (@lem1039263 (term368 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039265 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : ((term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term379 _17162 _17163 _17167 _17166 _17164 _17165)) = True.
Proof. exact (TRANS (@lem1039260 _17162 _17163 _17164 _17167 _17165 _17166) (@lem1039264 _17162 _17163 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039266 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : True = ((term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term379 _17162 _17163 _17167 _17166 _17164 _17165)).
Proof. exact (SYM (@lem1039265 _17162 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039267 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term295 _17162 _17163 _17164 _17165 _17166 _17167) = (term379 _17162 _17163 _17167 _17166 _17164 _17165).
Proof. exact (EQ_MP (@lem1039266 _17162 _17163 _17167 _17166 _17164 _17165) (@lem0)). Qed.
Lemma lem1039268 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) (h1 : term107) : term379 _17162 _17163 _17167 _17166 _17164 _17165.
Proof. exact (EQ_MP (@lem1039267 _17162 _17163 _17167 _17166 _17164 _17165) (@lem1038478 _17162 _17163 _17164 _17165 _17166 _17167 h1)). Qed.
Lemma lem1039270 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1039271 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term379 _17162 _17163 _17167 _17166 _17164 _17165) = (term382 _17162 _17163 _17164 _17165 _17166 _17167).
Proof. exact (@lem1039270 (term376 _17162 _17163 _17167 _17166 _17164 _17165) (_17166 = _17167)). Qed.
Lemma lem1039273 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039274 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term383 _17162 _17163 _17167 _17166 _17164 _17165) = (term384 _17162 _17163 _17167 _17166 _17164 _17165).
Proof. exact (@lem1039273 (term296 _17164 _17165 _17162) (term373 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039276 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039277 (_17164 : nat) (_17165 : nat) (_17162 : nat) : (term385 _17164 _17165 _17162) = (_17164 = (Nat.add _17165 _17162)).
Proof. exact (@lem1039276 (_17164 = (Nat.add _17165 _17162))). Qed.
Lemma lem1039278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039279 (_17164 : nat) (_17165 : nat) (_17162 : nat) : (term386 _17164 _17165 _17162) = (term387 _17164 _17165 _17162).
Proof. exact (MK_COMB (@lem1039278) (@lem1039277 _17164 _17165 _17162)). Qed.
Lemma lem1039281 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039282 (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term388 _17163 _17167 _17166 _17164 _17165) = (term389 _17163 _17167 _17166 _17164 _17165).
Proof. exact (@lem1039281 (term296 _17166 _17167 _17163) (term371 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039284 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039285 (_17166 : nat) (_17167 : nat) (_17163 : nat) : (term385 _17166 _17167 _17163) = (_17166 = (Nat.add _17167 _17163)).
Proof. exact (@lem1039284 (_17166 = (Nat.add _17167 _17163))). Qed.
Lemma lem1039286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039287 (_17166 : nat) (_17167 : nat) (_17163 : nat) : (term386 _17166 _17167 _17163) = (term387 _17166 _17167 _17163).
Proof. exact (MK_COMB (@lem1039286) (@lem1039285 _17166 _17167 _17163)). Qed.
Lemma lem1039289 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039290 (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term390 _17167 _17166 _17164 _17165) = (term391 _17167 _17166 _17164 _17165).
Proof. exact (@lem1039289 (term352 _17164 _17167 _17165 _17166) (_17164 = _17165)). Qed.
Lemma lem1039292 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039293 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term392 _17164 _17167 _17165 _17166) = ((term53 _17164 _17166 _17165 _17167) = (term53 _17164 _17167 _17165 _17166)).
Proof. exact (@lem1039292 ((term53 _17164 _17166 _17165 _17167) = (term53 _17164 _17167 _17165 _17166))). Qed.
Lemma lem1039294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039295 (_17164 : nat) (_17167 : nat) (_17165 : nat) (_17166 : nat) : (term393 _17164 _17167 _17165 _17166) = (term394 _17164 _17167 _17165 _17166).
Proof. exact (MK_COMB (@lem1039294) (@lem1039293 _17164 _17167 _17165 _17166)). Qed.
Lemma lem1039296 (_17164 : nat) (_17165 : nat) : (term260 _17164 _17165) = (term260 _17164 _17165).
Proof. exact (eq_refl (term260 _17164 _17165)). Qed.
Lemma lem1039297 (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term391 _17167 _17166 _17164 _17165) = (term395 _17167 _17166 _17164 _17165).
Proof. exact (MK_COMB (@lem1039295 _17164 _17167 _17165 _17166) (@lem1039296 _17164 _17165)). Qed.
Lemma lem1039298 (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term390 _17167 _17166 _17164 _17165) = (term395 _17167 _17166 _17164 _17165).
Proof. exact (TRANS (@lem1039290 _17167 _17166 _17164 _17165) (@lem1039297 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039299 (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term389 _17163 _17167 _17166 _17164 _17165) = (term396 _17163 _17167 _17166 _17164 _17165).
Proof. exact (MK_COMB (@lem1039287 _17166 _17167 _17163) (@lem1039298 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039300 (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term388 _17163 _17167 _17166 _17164 _17165) = (term396 _17163 _17167 _17166 _17164 _17165).
Proof. exact (TRANS (@lem1039282 _17163 _17167 _17166 _17164 _17165) (@lem1039299 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039301 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term384 _17162 _17163 _17167 _17166 _17164 _17165) = (term397 _17162 _17163 _17167 _17166 _17164 _17165).
Proof. exact (MK_COMB (@lem1039279 _17164 _17165 _17162) (@lem1039300 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039302 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term383 _17162 _17163 _17167 _17166 _17164 _17165) = (term397 _17162 _17163 _17167 _17166 _17164 _17165).
Proof. exact (TRANS (@lem1039274 _17162 _17163 _17167 _17166 _17164 _17165) (@lem1039301 _17162 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039303 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1039304 (_17162 : nat) (_17163 : nat) (_17167 : nat) (_17166 : nat) (_17164 : nat) (_17165 : nat) : (term398 _17162 _17163 _17167 _17166 _17164 _17165) = (term399 _17162 _17163 _17167 _17166 _17164 _17165).
Proof. exact (MK_COMB (@lem1039303) (@lem1039302 _17162 _17163 _17167 _17166 _17164 _17165)). Qed.
Lemma lem1039305 (_17166 : nat) (_17167 : nat) : (_17166 = _17167) = (_17166 = _17167).
Proof. exact (eq_refl (_17166 = _17167)). Qed.
Lemma lem1039306 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term382 _17162 _17163 _17164 _17165 _17166 _17167) = (term400 _17162 _17163 _17164 _17165 _17166 _17167).
Proof. exact (MK_COMB (@lem1039304 _17162 _17163 _17167 _17166 _17164 _17165) (@lem1039305 _17166 _17167)). Qed.
Lemma lem1039307 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) : (term379 _17162 _17163 _17167 _17166 _17164 _17165) = (term400 _17162 _17163 _17164 _17165 _17166 _17167).
Proof. exact (TRANS (@lem1039271 _17162 _17163 _17164 _17165 _17166 _17167) (@lem1039306 _17162 _17163 _17164 _17165 _17166 _17167)). Qed.
Lemma lem1039309 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term401 z d d' w.
Proof. exact (conj (@lem1038837 w d' d z h1 h2) (@lem1038884 w d' d z h2)). Qed.
Lemma lem1039310 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term402 z d d' w.
Proof. exact (conj (@lem1038678 z d) (@lem1039309 w d' d z h1 h2)). Qed.
Lemma lem1039311 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term531 w d' d z) : term403 z d d' w.
Proof. exact (conj (@lem1038670 w d') (@lem1039310 w d' d z h1 h2)). Qed.
Lemma lem1039313 (_17162 : nat) (_17163 : nat) (_17164 : nat) (_17165 : nat) (_17166 : nat) (_17167 : nat) (h1 : term107) : term400 _17162 _17163 _17164 _17165 _17166 _17167.
Proof. exact (EQ_MP (@lem1039307 _17162 _17163 _17164 _17165 _17166 _17167) (@lem1039268 _17162 _17163 _17167 _17166 _17164 _17165 h1)). Qed.
Lemma lem1039314 (d' : nat) (w : nat) (d : nat) (z : nat) (h1 : term107) : term404 d' w d z.
Proof. exact (@lem1039313 d' d (Nat.add w d') w (Nat.add z d) z h1). Qed.
Lemma lem1039317 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : (Nat.add z d) = z.
Proof. exact (@lem1039314 d' w d z h1 (@lem1039311 w d' d z h2 h3)). Qed.
Lemma lem1039318 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : term405 d z.
Proof. exact (fun h0 : term349 d z => @lem1039317 w d' d z h1 h2 h3). Qed.
Lemma lem1039320 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039321 (d : nat) (z : nat) : (term405 d z) = ((Nat.add z d) = z).
Proof. exact (@lem1039320 ((Nat.add z d) = z)). Qed.
Lemma lem1039322 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : (Nat.add z d) = z.
Proof. exact (EQ_MP (@lem1039321 d z) (@lem1039318 w d' d z h1 h2 h3)). Qed.
Lemma lem1039325 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1039327 (d : nat) (z : nat) : (term349 d z) = (term546 d z).
Proof. exact (@lem1039325 ((Nat.add z d) = z)). Qed.
Lemma lem1039330 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term531 w d' d z) : term546 d z.
Proof. exact (EQ_MP (@lem1039327 d z) (@lem1038458 w d' d z h1)). Qed.
Lemma lem1039333 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : False.
Proof. exact (@lem1039330 w d' d z h3 (@lem1039322 w d' d z h1 h2 h3)). Qed.
Lemma lem1039334 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : term410.
Proof. exact (fun h0 : ~ False => @lem1039333 w d' d z h1 h2 h3). Qed.
Lemma lem1039336 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039337 : term410 = False.
Proof. exact (@lem1039336 False). Qed.
Lemma lem1039338 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : False.
Proof. exact (EQ_MP (@lem1039337) (@lem1039334 w d' d z h1 h2 h3)). Qed.
Lemma lem1039370 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1039372 (_17171 : nat) (_17170 : nat) (h1 : term216) : (Nat.add _17170 _17171) = (Nat.add _17171 _17170).
Proof. exact (EQ_MP (@lem1038387 _17171 _17170) (@lem1038386 _17170 _17171 h1)). Qed.
Lemma lem1039373 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : (term58 d' w z d) = (term150 d w d' z).
Proof. exact (@lem1039372 (term46 w z d) (term39 w d' z) h1). Qed.
Lemma lem1039374 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : term448 d w d' z.
Proof. exact (fun h0 : term449 d w d' z => @lem1039373 d w d' z h1). Qed.
Lemma lem1039376 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039377 (d : nat) (w : nat) (d' : nat) (z : nat) : (term448 d w d' z) = ((term58 d' w z d) = (term150 d w d' z)).
Proof. exact (@lem1039376 ((term58 d' w z d) = (term150 d w d' z))). Qed.
Lemma lem1039378 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : (term58 d' w z d) = (term150 d w d' z).
Proof. exact (EQ_MP (@lem1039377 d w d' z) (@lem1039374 d w d' z h1)). Qed.
Lemma lem1039380 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1039381 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1039380 (Nat.add w d')). Qed.
Lemma lem1039382 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1039381 w d'). Qed.
Lemma lem1039384 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039385 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1039384 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1039386 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1039385 w d') (@lem1039382 w d')). Qed.
Lemma lem1039388 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1039389 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1039388 (Nat.add z d)). Qed.
Lemma lem1039390 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1039389 z d). Qed.
Lemma lem1039392 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039393 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1039392 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1039394 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1039393 z d) (@lem1039390 z d)). Qed.
Lemma lem1039396 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (h1). Qed.
Lemma lem1039397 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term408 w d'.
Proof. exact (fun h0 : term294 w d' => @lem1039396 w d' h1). Qed.
Lemma lem1039399 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039400 (w : nat) (d' : nat) : (term408 w d') = (w = (Nat.add w d')).
Proof. exact (@lem1039399 (w = (Nat.add w d'))). Qed.
Lemma lem1039401 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : w = (Nat.add w d').
Proof. exact (EQ_MP (@lem1039400 w d') (@lem1039397 w d' h1)). Qed.
Lemma lem1039403 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1039404 (w : nat) : w = w.
Proof. exact (@lem1039403 w). Qed.
Lemma lem1039405 (w : nat) : term411 w.
Proof. exact (fun h0 : term412 w => @lem1039404 w). Qed.
Lemma lem1039407 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039408 (w : nat) : (term411 w) = (w = w).
Proof. exact (@lem1039407 (w = w)). Qed.
Lemma lem1039409 (w : nat) : w = w.
Proof. exact (EQ_MP (@lem1039408 w) (@lem1039405 w)). Qed.
Lemma lem1039427 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1039428 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1039427 (y = z) (term260 x z)). Qed.
Lemma lem1039438 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1039439 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1039438 x y) (@lem1039428 y x z)). Qed.
Lemma lem1039443 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039444 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1039443 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1039466 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1039439 y x z) (@lem1039444 y x z)). Qed.
Lemma lem1039467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1039468 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1039467) (@lem1039466 y x z)). Qed.
Lemma lem1039490 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1039491 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1039468 y x z) (@lem1039490 y x z)). Qed.
Lemma lem1039493 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1039494 (x : Prop) : (x = x) = True.
Proof. exact (@lem1039493 Prop x). Qed.
Lemma lem1039495 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1039494 (term310 y x z)). Qed.
Lemma lem1039496 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1039491 y x z) (@lem1039495 y x z)). Qed.
Lemma lem1039497 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1039496 y x z)). Qed.
Lemma lem1039498 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1039497 y x z) (@lem0)). Qed.
Lemma lem1039499 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1039498 y x z) (@lem1039370 x y z)). Qed.
Lemma lem1039501 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1039502 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1039501 (term315 y x z) (y = z)). Qed.
Lemma lem1039504 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039505 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1039504 (term260 x y) (term260 x z)). Qed.
Lemma lem1039507 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039508 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1039507 (x = y)). Qed.
Lemma lem1039509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039510 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1039509) (@lem1039508 x y)). Qed.
Lemma lem1039512 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039513 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1039512 (x = z)). Qed.
Lemma lem1039514 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1039510 x y) (@lem1039513 x z)). Qed.
Lemma lem1039515 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1039505 y x z) (@lem1039514 y x z)). Qed.
Lemma lem1039516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1039517 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1039516) (@lem1039515 y x z)). Qed.
Lemma lem1039518 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1039519 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1039517 y x z) (@lem1039518 y z)). Qed.
Lemma lem1039520 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1039502 x y z) (@lem1039519 x y z)). Qed.
Lemma lem1039522 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term413 d' w.
Proof. exact (conj (@lem1039401 w d' h1) (@lem1039409 w)). Qed.
Lemma lem1039524 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1039520 x y z) (@lem1039499 y x z)). Qed.
Lemma lem1039525 (d' : nat) (w : nat) : term414 d' w.
Proof. exact (@lem1039524 w (Nat.add w d') w). Qed.
Lemma lem1039528 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : (Nat.add w d') = w.
Proof. exact (@lem1039525 d' w (@lem1039522 w d' h1)). Qed.
Lemma lem1039529 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term405 d' w.
Proof. exact (fun h0 : term349 d' w => @lem1039528 w d' h1). Qed.
Lemma lem1039531 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039532 (d' : nat) (w : nat) : (term405 d' w) = ((Nat.add w d') = w).
Proof. exact (@lem1039531 ((Nat.add w d') = w)). Qed.
Lemma lem1039533 (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : (Nat.add w d') = w.
Proof. exact (EQ_MP (@lem1039532 d' w) (@lem1039529 w d' h1)). Qed.
Lemma lem1039551 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039552 (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term415 _17173 _17177 _17176 _17174 _17175) = (term416 _17176 _17177 _17173 _17174 _17175).
Proof. exact (@lem1039551 ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176)) (term296 _17176 _17177 _17173) (term260 _17174 _17175)). Qed.
Lemma lem1039568 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1039569 (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term417 _17176 _17177 _17173 _17174 _17175) = (term418 _17174 _17175 _17176 _17177 _17173).
Proof. exact (@lem1039568 (term260 _17174 _17175) (term296 _17176 _17177 _17173)). Qed.
Lemma lem1039579 (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term236 _17174 _17177 _17175 _17176) = (term236 _17174 _17177 _17175 _17176).
Proof. exact (eq_refl (term236 _17174 _17177 _17175 _17176)). Qed.
Lemma lem1039580 (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term416 _17176 _17177 _17173 _17174 _17175) = (term419 _17174 _17175 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039579 _17174 _17177 _17175 _17176) (@lem1039569 _17174 _17175 _17176 _17177 _17173)). Qed.
Lemma lem1039591 (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term415 _17173 _17177 _17176 _17174 _17175) = (term419 _17174 _17175 _17176 _17177 _17173).
Proof. exact (TRANS (@lem1039552 _17176 _17177 _17173 _17174 _17175) (@lem1039580 _17174 _17175 _17176 _17177 _17173)). Qed.
Lemma lem1039592 (_17174 : nat) (_17175 : nat) (_17172 : nat) : (term356 _17174 _17175 _17172) = (term356 _17174 _17175 _17172).
Proof. exact (eq_refl (term356 _17174 _17175 _17172)). Qed.
Lemma lem1039593 (_17172 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term420 _17172 _17174 _17175 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039592 _17174 _17175 _17172) (@lem1039591 _17174 _17175 _17176 _17177 _17173)). Qed.
Lemma lem1039597 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039598 (_17172 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term420 _17172 _17174 _17175 _17176 _17177 _17173) = (term421 _17172 _17174 _17175 _17176 _17177 _17173).
Proof. exact (@lem1039597 ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176)) (term296 _17174 _17175 _17172) (term418 _17174 _17175 _17176 _17177 _17173)). Qed.
Lemma lem1039614 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039615 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term422 _17172 _17174 _17175 _17176 _17177 _17173) = (term423 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (@lem1039614 (term260 _17174 _17175) (term296 _17174 _17175 _17172) (term296 _17176 _17177 _17173)). Qed.
Lemma lem1039637 (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term236 _17174 _17177 _17175 _17176) = (term236 _17174 _17177 _17175 _17176).
Proof. exact (eq_refl (term236 _17174 _17177 _17175 _17176)). Qed.
Lemma lem1039638 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term421 _17172 _17174 _17175 _17176 _17177 _17173) = (term424 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039637 _17174 _17177 _17175 _17176) (@lem1039615 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039649 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term420 _17172 _17174 _17175 _17176 _17177 _17173) = (term424 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (TRANS (@lem1039598 _17172 _17174 _17175 _17176 _17177 _17173) (@lem1039638 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039650 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term424 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (TRANS (@lem1039593 _17172 _17174 _17175 _17176 _17177 _17173) (@lem1039649 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1039652 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term425 _17172 _17173 _17177 _17176 _17174 _17175) = (term426 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039651) (@lem1039650 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039680 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1039681 (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term417 _17176 _17177 _17173 _17174 _17175) = (term418 _17174 _17175 _17176 _17177 _17173).
Proof. exact (@lem1039680 (term260 _17174 _17175) (term296 _17176 _17177 _17173)). Qed.
Lemma lem1039691 (_17174 : nat) (_17175 : nat) (_17172 : nat) : (term356 _17174 _17175 _17172) = (term356 _17174 _17175 _17172).
Proof. exact (eq_refl (term356 _17174 _17175 _17172)). Qed.
Lemma lem1039692 (_17172 : nat) (_17174 : nat) (_17175 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term427 _17172 _17176 _17177 _17173 _17174 _17175) = (term422 _17172 _17174 _17175 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039691 _17174 _17175 _17172) (@lem1039681 _17174 _17175 _17176 _17177 _17173)). Qed.
Lemma lem1039696 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039697 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term422 _17172 _17174 _17175 _17176 _17177 _17173) = (term423 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (@lem1039696 (term260 _17174 _17175) (term296 _17174 _17175 _17172) (term296 _17176 _17177 _17173)). Qed.
Lemma lem1039719 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term427 _17172 _17176 _17177 _17173 _17174 _17175) = (term423 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (TRANS (@lem1039692 _17172 _17174 _17175 _17176 _17177 _17173) (@lem1039697 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039720 (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term236 _17174 _17177 _17175 _17176) = (term236 _17174 _17177 _17175 _17176).
Proof. exact (eq_refl (term236 _17174 _17177 _17175 _17176)). Qed.
Lemma lem1039721 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term428 _17172 _17176 _17177 _17173 _17174 _17175) = (term424 _17174 _17175 _17172 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039720 _17174 _17177 _17175 _17176) (@lem1039719 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039732 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : ((term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term428 _17172 _17176 _17177 _17173 _17174 _17175)) = ((term424 _17174 _17175 _17172 _17176 _17177 _17173) = (term424 _17174 _17175 _17172 _17176 _17177 _17173)).
Proof. exact (MK_COMB (@lem1039652 _17174 _17175 _17172 _17176 _17177 _17173) (@lem1039721 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039734 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1039735 (x : Prop) : (x = x) = True.
Proof. exact (@lem1039734 Prop x). Qed.
Lemma lem1039736 (_17174 : nat) (_17175 : nat) (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) : ((term424 _17174 _17175 _17172 _17176 _17177 _17173) = (term424 _17174 _17175 _17172 _17176 _17177 _17173)) = True.
Proof. exact (@lem1039735 (term424 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039737 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : ((term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term428 _17172 _17176 _17177 _17173 _17174 _17175)) = True.
Proof. exact (TRANS (@lem1039732 _17174 _17175 _17172 _17176 _17177 _17173) (@lem1039736 _17174 _17175 _17172 _17176 _17177 _17173)). Qed.
Lemma lem1039738 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : True = ((term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term428 _17172 _17176 _17177 _17173 _17174 _17175)).
Proof. exact (SYM (@lem1039737 _17172 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039739 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term298 _17172 _17173 _17177 _17176 _17174 _17175) = (term428 _17172 _17176 _17177 _17173 _17174 _17175).
Proof. exact (EQ_MP (@lem1039738 _17172 _17176 _17177 _17173 _17174 _17175) (@lem0)). Qed.
Lemma lem1039740 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) (h1 : term107) : term428 _17172 _17176 _17177 _17173 _17174 _17175.
Proof. exact (EQ_MP (@lem1039739 _17172 _17176 _17177 _17173 _17174 _17175) (@lem1038554 _17172 _17173 _17177 _17176 _17174 _17175 h1)). Qed.
Lemma lem1039742 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1039743 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term428 _17172 _17176 _17177 _17173 _17174 _17175) = (term429 _17172 _17173 _17174 _17177 _17175 _17176).
Proof. exact (@lem1039742 (term427 _17172 _17176 _17177 _17173 _17174 _17175) ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176))). Qed.
Lemma lem1039745 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039746 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term430 _17172 _17176 _17177 _17173 _17174 _17175) = (term431 _17172 _17176 _17177 _17173 _17174 _17175).
Proof. exact (@lem1039745 (term296 _17174 _17175 _17172) (term417 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039748 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039749 (_17174 : nat) (_17175 : nat) (_17172 : nat) : (term385 _17174 _17175 _17172) = (_17174 = (Nat.add _17175 _17172)).
Proof. exact (@lem1039748 (_17174 = (Nat.add _17175 _17172))). Qed.
Lemma lem1039750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039751 (_17174 : nat) (_17175 : nat) (_17172 : nat) : (term386 _17174 _17175 _17172) = (term387 _17174 _17175 _17172).
Proof. exact (MK_COMB (@lem1039750) (@lem1039749 _17174 _17175 _17172)). Qed.
Lemma lem1039753 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1039754 (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term432 _17176 _17177 _17173 _17174 _17175) = (term433 _17176 _17177 _17173 _17174 _17175).
Proof. exact (@lem1039753 (term296 _17176 _17177 _17173) (term260 _17174 _17175)). Qed.
Lemma lem1039756 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039757 (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term385 _17176 _17177 _17173) = (_17176 = (Nat.add _17177 _17173)).
Proof. exact (@lem1039756 (_17176 = (Nat.add _17177 _17173))). Qed.
Lemma lem1039758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1039759 (_17176 : nat) (_17177 : nat) (_17173 : nat) : (term386 _17176 _17177 _17173) = (term387 _17176 _17177 _17173).
Proof. exact (MK_COMB (@lem1039758) (@lem1039757 _17176 _17177 _17173)). Qed.
Lemma lem1039761 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1039762 (_17174 : nat) (_17175 : nat) : (term321 _17174 _17175) = (_17174 = _17175).
Proof. exact (@lem1039761 (_17174 = _17175)). Qed.
Lemma lem1039763 (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term433 _17176 _17177 _17173 _17174 _17175) = (term434 _17176 _17177 _17173 _17174 _17175).
Proof. exact (MK_COMB (@lem1039759 _17176 _17177 _17173) (@lem1039762 _17174 _17175)). Qed.
Lemma lem1039764 (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term432 _17176 _17177 _17173 _17174 _17175) = (term434 _17176 _17177 _17173 _17174 _17175).
Proof. exact (TRANS (@lem1039754 _17176 _17177 _17173 _17174 _17175) (@lem1039763 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039765 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term431 _17172 _17176 _17177 _17173 _17174 _17175) = (term435 _17172 _17176 _17177 _17173 _17174 _17175).
Proof. exact (MK_COMB (@lem1039751 _17174 _17175 _17172) (@lem1039764 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039766 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term430 _17172 _17176 _17177 _17173 _17174 _17175) = (term435 _17172 _17176 _17177 _17173 _17174 _17175).
Proof. exact (TRANS (@lem1039746 _17172 _17176 _17177 _17173 _17174 _17175) (@lem1039765 _17172 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1039768 (_17172 : nat) (_17176 : nat) (_17177 : nat) (_17173 : nat) (_17174 : nat) (_17175 : nat) : (term436 _17172 _17176 _17177 _17173 _17174 _17175) = (term437 _17172 _17176 _17177 _17173 _17174 _17175).
Proof. exact (MK_COMB (@lem1039767) (@lem1039766 _17172 _17176 _17177 _17173 _17174 _17175)). Qed.
Lemma lem1039769 (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176)) = ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176)).
Proof. exact (eq_refl ((term53 _17174 _17176 _17175 _17177) = (term53 _17174 _17177 _17175 _17176))). Qed.
Lemma lem1039770 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term429 _17172 _17173 _17174 _17177 _17175 _17176) = (term438 _17172 _17173 _17174 _17177 _17175 _17176).
Proof. exact (MK_COMB (@lem1039768 _17172 _17176 _17177 _17173 _17174 _17175) (@lem1039769 _17174 _17177 _17175 _17176)). Qed.
Lemma lem1039771 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) : (term428 _17172 _17176 _17177 _17173 _17174 _17175) = (term438 _17172 _17173 _17174 _17177 _17175 _17176).
Proof. exact (TRANS (@lem1039743 _17172 _17173 _17174 _17177 _17175 _17176) (@lem1039770 _17172 _17173 _17174 _17177 _17175 _17176)). Qed.
Lemma lem1039773 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term439 z d d' w.
Proof. exact (conj (@lem1039394 z d) (@lem1039533 w d' h1)). Qed.
Lemma lem1039774 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : w = (Nat.add w d')) : term440 z d d' w.
Proof. exact (conj (@lem1039386 w d') (@lem1039773 z d w d' h1)). Qed.
Lemma lem1039776 (_17172 : nat) (_17173 : nat) (_17174 : nat) (_17177 : nat) (_17175 : nat) (_17176 : nat) (h1 : term107) : term438 _17172 _17173 _17174 _17177 _17175 _17176.
Proof. exact (EQ_MP (@lem1039771 _17172 _17173 _17174 _17177 _17175 _17176) (@lem1039740 _17172 _17176 _17177 _17173 _17174 _17175 h1)). Qed.
Lemma lem1039777 (d' : nat) (w : nat) (z : nat) (d : nat) (h1 : term107) : term441 d' w z d.
Proof. exact (@lem1039776 d' d (Nat.add w d') z w (Nat.add z d) h1). Qed.
Lemma lem1039780 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (@lem1039777 d' w z d h1 (@lem1039774 z d w d' h2)). Qed.
Lemma lem1039781 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : term336 d' w z d.
Proof. exact (fun h0 : term337 d' w z d => @lem1039780 z d w d' h1 h2). Qed.
Lemma lem1039783 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039784 (d' : nat) (w : nat) (z : nat) (d : nat) : (term336 d' w z d) = ((term54 d' d w z) = (term58 d' w z d)).
Proof. exact (@lem1039783 ((term54 d' d w z) = (term58 d' w z d))). Qed.
Lemma lem1039785 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : w = (Nat.add w d')) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (EQ_MP (@lem1039784 d' w z d) (@lem1039781 z d w d' h1 h2)). Qed.
Lemma lem1039787 (_17171 : nat) (_17170 : nat) (h1 : term216) : (Nat.add _17170 _17171) = (Nat.add _17171 _17170).
Proof. exact (EQ_MP (@lem1038387 _17171 _17170) (@lem1038386 _17170 _17171 h1)). Qed.
Lemma lem1039788 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : (term54 d' d w z) = (term149 w d' z d).
Proof. exact (@lem1039787 (Nat.mul w z) (term50 w d' z d) h1). Qed.
Lemma lem1039789 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : term442 w d' z d.
Proof. exact (fun h0 : term443 w d' z d => @lem1039788 w d' z d h1). Qed.
Lemma lem1039791 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039792 (w : nat) (d' : nat) (z : nat) (d : nat) : (term442 w d' z d) = ((term54 d' d w z) = (term149 w d' z d)).
Proof. exact (@lem1039791 ((term54 d' d w z) = (term149 w d' z d))). Qed.
Lemma lem1039793 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : (term54 d' d w z) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1039792 w d' z d) (@lem1039789 w d' z d h1)). Qed.
Lemma lem1039794 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term444 w d' z d.
Proof. exact (conj (@lem1039785 z d w d' h1 h3) (@lem1039793 w d' z d h2)). Qed.
Lemma lem1039796 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1039520 x y z) (@lem1039499 y x z)). Qed.
Lemma lem1039797 (w : nat) (d' : nat) (z : nat) (d : nat) : term445 w d' z d.
Proof. exact (@lem1039796 (term54 d' d w z) (term58 d' w z d) (term149 w d' z d)). Qed.
Lemma lem1039800 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term58 d' w z d) = (term149 w d' z d).
Proof. exact (@lem1039797 w d' z d (@lem1039794 z d w d' h1 h2 h3)). Qed.
Lemma lem1039801 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term446 w d' z d.
Proof. exact (fun h0 : term447 w d' z d => @lem1039800 z d w d' h1 h2 h3). Qed.
Lemma lem1039803 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039804 (w : nat) (d' : nat) (z : nat) (d : nat) : (term446 w d' z d) = ((term58 d' w z d) = (term149 w d' z d)).
Proof. exact (@lem1039803 ((term58 d' w z d) = (term149 w d' z d))). Qed.
Lemma lem1039805 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term58 d' w z d) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1039804 w d' z d) (@lem1039801 z d w d' h1 h2 h3)). Qed.
Lemma lem1039806 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term547 w d' z d.
Proof. exact (conj (@lem1039378 d w d' z h2) (@lem1039805 z d w d' h1 h2 h3)). Qed.
Lemma lem1039808 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1039520 x y z) (@lem1039499 y x z)). Qed.
Lemma lem1039809 (w : nat) (d' : nat) (z : nat) (d : nat) : term548 w d' z d.
Proof. exact (@lem1039808 (term58 d' w z d) (term150 d w d' z) (term149 w d' z d)). Qed.
Lemma lem1039812 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (@lem1039809 w d' z d (@lem1039806 z d w d' h1 h2 h3)). Qed.
Lemma lem1039813 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : term539 w d' z d.
Proof. exact (fun h0 : term537 w d' z d => @lem1039812 z d w d' h1 h2 h3). Qed.
Lemma lem1039815 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039816 (w : nat) (d' : nat) (z : nat) (d : nat) : (term539 w d' z d) = ((term150 d w d' z) = (term149 w d' z d)).
Proof. exact (@lem1039815 ((term150 d w d' z) = (term149 w d' z d))). Qed.
Lemma lem1039817 (z : nat) (d : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : w = (Nat.add w d')) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1039816 w d' z d) (@lem1039813 z d w d' h1 h2 h3)). Qed.
Lemma lem1039820 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1039822 (w : nat) (d' : nat) (z : nat) (d : nat) : (term537 w d' z d) = (term549 w d' z d).
Proof. exact (@lem1039820 ((term150 d w d' z) = (term149 w d' z d))). Qed.
Lemma lem1039825 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term549 w d' z d.
Proof. exact (EQ_MP (@lem1039822 w d' z d) (@lem1038516 w d' d z h1)). Qed.
Lemma lem1039828 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (@lem1039825 w d' d z h3 (@lem1039817 z d w d' h1 h2 h4)). Qed.
Lemma lem1039829 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : term410.
Proof. exact (fun h0 : ~ False => @lem1039828 d z w d' h1 h2 h3 h4). Qed.
Lemma lem1039831 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039832 : term410 = False.
Proof. exact (@lem1039831 False). Qed.
Lemma lem1039833 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1039832) (@lem1039829 d z w d' h1 h2 h3 h4)). Qed.
Lemma lem1039865 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1039867 (_17181 : nat) (_17180 : nat) (h1 : term216) : (Nat.add _17180 _17181) = (Nat.add _17181 _17180).
Proof. exact (EQ_MP (@lem1038417 _17181 _17180) (@lem1038416 _17180 _17181 h1)). Qed.
Lemma lem1039868 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : (term58 d' w z d) = (term150 d w d' z).
Proof. exact (@lem1039867 (term46 w z d) (term39 w d' z) h1). Qed.
Lemma lem1039869 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : term448 d w d' z.
Proof. exact (fun h0 : term449 d w d' z => @lem1039868 d w d' z h1). Qed.
Lemma lem1039871 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039872 (d : nat) (w : nat) (d' : nat) (z : nat) : (term448 d w d' z) = ((term58 d' w z d) = (term150 d w d' z)).
Proof. exact (@lem1039871 ((term58 d' w z d) = (term150 d w d' z))). Qed.
Lemma lem1039873 (d : nat) (w : nat) (d' : nat) (z : nat) (h1 : term216) : (term58 d' w z d) = (term150 d w d' z).
Proof. exact (EQ_MP (@lem1039872 d w d' z) (@lem1039869 d w d' z h1)). Qed.
Lemma lem1039875 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1039876 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (@lem1039875 (Nat.add w d')). Qed.
Lemma lem1039877 (w : nat) (d' : nat) : term300 w d'.
Proof. exact (fun h0 : term301 w d' => @lem1039876 w d'). Qed.
Lemma lem1039879 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039880 (w : nat) (d' : nat) : (term300 w d') = ((Nat.add w d') = (Nat.add w d')).
Proof. exact (@lem1039879 ((Nat.add w d') = (Nat.add w d'))). Qed.
Lemma lem1039881 (w : nat) (d' : nat) : (Nat.add w d') = (Nat.add w d').
Proof. exact (EQ_MP (@lem1039880 w d') (@lem1039877 w d')). Qed.
Lemma lem1039883 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1039884 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1039883 (Nat.add z d)). Qed.
Lemma lem1039885 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1039884 z d). Qed.
Lemma lem1039887 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039888 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1039887 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1039889 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1039888 z d) (@lem1039885 z d)). Qed.
Lemma lem1039891 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1039892 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term405 d z.
Proof. exact (fun h0 : term349 d z => @lem1039891 d z h1). Qed.
Lemma lem1039894 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1039895 (d : nat) (z : nat) : (term405 d z) = ((Nat.add z d) = z).
Proof. exact (@lem1039894 ((Nat.add z d) = z)). Qed.
Lemma lem1039896 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (EQ_MP (@lem1039895 d z) (@lem1039892 d z h1)). Qed.
Lemma lem1039914 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039915 (_17184 : nat) (_17185 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term550 _17183 _17184 _17185 _17186 _17187) = (term551 _17184 _17185 _17183 _17186 _17187).
Proof. exact (@lem1039914 ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186)) (term296 _17186 _17187 _17183) (term260 _17186 _17187)). Qed.
Lemma lem1039931 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1039932 (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term552 _17183 _17186 _17187) = (term553 _17186 _17187 _17183).
Proof. exact (@lem1039931 (term260 _17186 _17187) (term296 _17186 _17187 _17183)). Qed.
Lemma lem1039942 (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : (term236 _17184 _17187 _17185 _17186) = (term236 _17184 _17187 _17185 _17186).
Proof. exact (eq_refl (term236 _17184 _17187 _17185 _17186)). Qed.
Lemma lem1039943 (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term551 _17184 _17185 _17183 _17186 _17187) = (term554 _17184 _17185 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1039942 _17184 _17187 _17185 _17186) (@lem1039932 _17186 _17187 _17183)). Qed.
Lemma lem1039954 (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term550 _17183 _17184 _17185 _17186 _17187) = (term554 _17184 _17185 _17186 _17187 _17183).
Proof. exact (TRANS (@lem1039915 _17184 _17185 _17183 _17186 _17187) (@lem1039943 _17184 _17185 _17186 _17187 _17183)). Qed.
Lemma lem1039955 (_17184 : nat) (_17185 : nat) (_17182 : nat) : (term356 _17184 _17185 _17182) = (term356 _17184 _17185 _17182).
Proof. exact (eq_refl (term356 _17184 _17185 _17182)). Qed.
Lemma lem1039956 (_17182 : nat) (_17184 : nat) (_17185 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term555 _17182 _17184 _17185 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1039955 _17184 _17185 _17182) (@lem1039954 _17184 _17185 _17186 _17187 _17183)). Qed.
Lemma lem1039960 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1039961 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term555 _17182 _17184 _17185 _17186 _17187 _17183) = (term556 _17184 _17185 _17182 _17186 _17187 _17183).
Proof. exact (@lem1039960 ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186)) (term296 _17184 _17185 _17182) (term553 _17186 _17187 _17183)). Qed.
Lemma lem1039995 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term556 _17184 _17185 _17182 _17186 _17187 _17183).
Proof. exact (TRANS (@lem1039956 _17182 _17184 _17185 _17186 _17187 _17183) (@lem1039961 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1039996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1039997 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term557 _17182 _17183 _17184 _17185 _17186 _17187) = (term558 _17184 _17185 _17182 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1039996) (@lem1039995 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1040025 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1040026 (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term552 _17183 _17186 _17187) = (term553 _17186 _17187 _17183).
Proof. exact (@lem1040025 (term260 _17186 _17187) (term296 _17186 _17187 _17183)). Qed.
Lemma lem1040036 (_17184 : nat) (_17185 : nat) (_17182 : nat) : (term356 _17184 _17185 _17182) = (term356 _17184 _17185 _17182).
Proof. exact (eq_refl (term356 _17184 _17185 _17182)). Qed.
Lemma lem1040037 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term559 _17184 _17185 _17182 _17183 _17186 _17187) = (term560 _17184 _17185 _17182 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1040036 _17184 _17185 _17182) (@lem1040026 _17186 _17187 _17183)). Qed.
Lemma lem1040048 (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : (term236 _17184 _17187 _17185 _17186) = (term236 _17184 _17187 _17185 _17186).
Proof. exact (eq_refl (term236 _17184 _17187 _17185 _17186)). Qed.
Lemma lem1040049 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term561 _17184 _17185 _17182 _17183 _17186 _17187) = (term556 _17184 _17185 _17182 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1040048 _17184 _17187 _17185 _17186) (@lem1040037 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1040060 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : ((term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term561 _17184 _17185 _17182 _17183 _17186 _17187)) = ((term556 _17184 _17185 _17182 _17186 _17187 _17183) = (term556 _17184 _17185 _17182 _17186 _17187 _17183)).
Proof. exact (MK_COMB (@lem1039997 _17184 _17185 _17182 _17186 _17187 _17183) (@lem1040049 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1040062 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1040063 (x : Prop) : (x = x) = True.
Proof. exact (@lem1040062 Prop x). Qed.
Lemma lem1040064 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17186 : nat) (_17187 : nat) (_17183 : nat) : ((term556 _17184 _17185 _17182 _17186 _17187 _17183) = (term556 _17184 _17185 _17182 _17186 _17187 _17183)) = True.
Proof. exact (@lem1040063 (term556 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1040065 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : ((term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term561 _17184 _17185 _17182 _17183 _17186 _17187)) = True.
Proof. exact (TRANS (@lem1040060 _17184 _17185 _17182 _17186 _17187 _17183) (@lem1040064 _17184 _17185 _17182 _17186 _17187 _17183)). Qed.
Lemma lem1040066 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : True = ((term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term561 _17184 _17185 _17182 _17183 _17186 _17187)).
Proof. exact (SYM (@lem1040065 _17184 _17185 _17182 _17183 _17186 _17187)). Qed.
Lemma lem1040067 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term538 _17182 _17183 _17184 _17185 _17186 _17187) = (term561 _17184 _17185 _17182 _17183 _17186 _17187).
Proof. exact (EQ_MP (@lem1040066 _17184 _17185 _17182 _17183 _17186 _17187) (@lem0)). Qed.
Lemma lem1040068 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) (h1 : term107) : term561 _17184 _17185 _17182 _17183 _17186 _17187.
Proof. exact (EQ_MP (@lem1040067 _17184 _17185 _17182 _17183 _17186 _17187) (@lem1038630 _17182 _17183 _17184 _17185 _17186 _17187 h1)). Qed.
Lemma lem1040070 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1040071 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : (term561 _17184 _17185 _17182 _17183 _17186 _17187) = (term562 _17182 _17183 _17184 _17187 _17185 _17186).
Proof. exact (@lem1040070 (term559 _17184 _17185 _17182 _17183 _17186 _17187) ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186))). Qed.
Lemma lem1040073 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1040074 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term563 _17184 _17185 _17182 _17183 _17186 _17187) = (term564 _17184 _17185 _17182 _17183 _17186 _17187).
Proof. exact (@lem1040073 (term296 _17184 _17185 _17182) (term552 _17183 _17186 _17187)). Qed.
Lemma lem1040076 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1040077 (_17184 : nat) (_17185 : nat) (_17182 : nat) : (term385 _17184 _17185 _17182) = (_17184 = (Nat.add _17185 _17182)).
Proof. exact (@lem1040076 (_17184 = (Nat.add _17185 _17182))). Qed.
Lemma lem1040078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1040079 (_17184 : nat) (_17185 : nat) (_17182 : nat) : (term386 _17184 _17185 _17182) = (term387 _17184 _17185 _17182).
Proof. exact (MK_COMB (@lem1040078) (@lem1040077 _17184 _17185 _17182)). Qed.
Lemma lem1040081 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1040082 (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term565 _17183 _17186 _17187) = (term566 _17183 _17186 _17187).
Proof. exact (@lem1040081 (term296 _17186 _17187 _17183) (term260 _17186 _17187)). Qed.
Lemma lem1040084 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1040085 (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term385 _17186 _17187 _17183) = (_17186 = (Nat.add _17187 _17183)).
Proof. exact (@lem1040084 (_17186 = (Nat.add _17187 _17183))). Qed.
Lemma lem1040086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1040087 (_17186 : nat) (_17187 : nat) (_17183 : nat) : (term386 _17186 _17187 _17183) = (term387 _17186 _17187 _17183).
Proof. exact (MK_COMB (@lem1040086) (@lem1040085 _17186 _17187 _17183)). Qed.
Lemma lem1040089 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1040090 (_17186 : nat) (_17187 : nat) : (term321 _17186 _17187) = (_17186 = _17187).
Proof. exact (@lem1040089 (_17186 = _17187)). Qed.
Lemma lem1040091 (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term566 _17183 _17186 _17187) = (term567 _17183 _17186 _17187).
Proof. exact (MK_COMB (@lem1040087 _17186 _17187 _17183) (@lem1040090 _17186 _17187)). Qed.
Lemma lem1040092 (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term565 _17183 _17186 _17187) = (term567 _17183 _17186 _17187).
Proof. exact (TRANS (@lem1040082 _17183 _17186 _17187) (@lem1040091 _17183 _17186 _17187)). Qed.
Lemma lem1040093 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term564 _17184 _17185 _17182 _17183 _17186 _17187) = (term568 _17184 _17185 _17182 _17183 _17186 _17187).
Proof. exact (MK_COMB (@lem1040079 _17184 _17185 _17182) (@lem1040092 _17183 _17186 _17187)). Qed.
Lemma lem1040094 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term563 _17184 _17185 _17182 _17183 _17186 _17187) = (term568 _17184 _17185 _17182 _17183 _17186 _17187).
Proof. exact (TRANS (@lem1040074 _17184 _17185 _17182 _17183 _17186 _17187) (@lem1040093 _17184 _17185 _17182 _17183 _17186 _17187)). Qed.
Lemma lem1040095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1040096 (_17184 : nat) (_17185 : nat) (_17182 : nat) (_17183 : nat) (_17186 : nat) (_17187 : nat) : (term569 _17184 _17185 _17182 _17183 _17186 _17187) = (term570 _17184 _17185 _17182 _17183 _17186 _17187).
Proof. exact (MK_COMB (@lem1040095) (@lem1040094 _17184 _17185 _17182 _17183 _17186 _17187)). Qed.
Lemma lem1040097 (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186)) = ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186)).
Proof. exact (eq_refl ((term53 _17184 _17186 _17185 _17187) = (term53 _17184 _17187 _17185 _17186))). Qed.
Lemma lem1040098 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : (term562 _17182 _17183 _17184 _17187 _17185 _17186) = (term571 _17182 _17183 _17184 _17187 _17185 _17186).
Proof. exact (MK_COMB (@lem1040096 _17184 _17185 _17182 _17183 _17186 _17187) (@lem1040097 _17184 _17187 _17185 _17186)). Qed.
Lemma lem1040099 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) : (term561 _17184 _17185 _17182 _17183 _17186 _17187) = (term571 _17182 _17183 _17184 _17187 _17185 _17186).
Proof. exact (TRANS (@lem1040071 _17182 _17183 _17184 _17187 _17185 _17186) (@lem1040098 _17182 _17183 _17184 _17187 _17185 _17186)). Qed.
Lemma lem1040101 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term572 d z.
Proof. exact (conj (@lem1039889 z d) (@lem1039896 d z h1)). Qed.
Lemma lem1040102 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term573 w d' d z.
Proof. exact (conj (@lem1039881 w d') (@lem1040101 d z h1)). Qed.
Lemma lem1040104 (_17182 : nat) (_17183 : nat) (_17184 : nat) (_17187 : nat) (_17185 : nat) (_17186 : nat) (h1 : term107) : term571 _17182 _17183 _17184 _17187 _17185 _17186.
Proof. exact (EQ_MP (@lem1040099 _17182 _17183 _17184 _17187 _17185 _17186) (@lem1040068 _17184 _17185 _17182 _17183 _17186 _17187 h1)). Qed.
Lemma lem1040105 (d' : nat) (w : nat) (z : nat) (d : nat) (h1 : term107) : term574 d' w z d.
Proof. exact (@lem1040104 d' d (Nat.add w d') z w (Nat.add z d) h1). Qed.
Lemma lem1040108 (d' : nat) (w : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (@lem1040105 d' w z d h1 (@lem1040102 w d' d z h2)). Qed.
Lemma lem1040109 (d' : nat) (w : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : term336 d' w z d.
Proof. exact (fun h0 : term337 d' w z d => @lem1040108 d' w d z h1 h2). Qed.
Lemma lem1040111 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1040112 (d' : nat) (w : nat) (z : nat) (d : nat) : (term336 d' w z d) = ((term54 d' d w z) = (term58 d' w z d)).
Proof. exact (@lem1040111 ((term54 d' d w z) = (term58 d' w z d))). Qed.
Lemma lem1040113 (d' : nat) (w : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : (term54 d' d w z) = (term58 d' w z d).
Proof. exact (EQ_MP (@lem1040112 d' w z d) (@lem1040109 d' w d z h1 h2)). Qed.
Lemma lem1040115 (_17181 : nat) (_17180 : nat) (h1 : term216) : (Nat.add _17180 _17181) = (Nat.add _17181 _17180).
Proof. exact (EQ_MP (@lem1038417 _17181 _17180) (@lem1038416 _17180 _17181 h1)). Qed.
Lemma lem1040116 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : (term54 d' d w z) = (term149 w d' z d).
Proof. exact (@lem1040115 (Nat.mul w z) (term50 w d' z d) h1). Qed.
Lemma lem1040117 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : term442 w d' z d.
Proof. exact (fun h0 : term443 w d' z d => @lem1040116 w d' z d h1). Qed.
Lemma lem1040119 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1040120 (w : nat) (d' : nat) (z : nat) (d : nat) : (term442 w d' z d) = ((term54 d' d w z) = (term149 w d' z d)).
Proof. exact (@lem1040119 ((term54 d' d w z) = (term149 w d' z d))). Qed.
Lemma lem1040121 (w : nat) (d' : nat) (z : nat) (d : nat) (h1 : term216) : (term54 d' d w z) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1040120 w d' z d) (@lem1040117 w d' z d h1)). Qed.
Lemma lem1040139 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1040140 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1040139 (y = z) (term260 x z)). Qed.
Lemma lem1040150 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1040151 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1040150 x y) (@lem1040140 y x z)). Qed.
Lemma lem1040155 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1040156 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1040155 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1040178 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1040151 y x z) (@lem1040156 y x z)). Qed.
Lemma lem1040179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1040180 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1040179) (@lem1040178 y x z)). Qed.
Lemma lem1040202 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1040203 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1040180 y x z) (@lem1040202 y x z)). Qed.
Lemma lem1040205 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1040206 (x : Prop) : (x = x) = True.
Proof. exact (@lem1040205 Prop x). Qed.
Lemma lem1040207 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1040206 (term310 y x z)). Qed.
Lemma lem1040208 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1040203 y x z) (@lem1040207 y x z)). Qed.
Lemma lem1040209 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1040208 y x z)). Qed.
Lemma lem1040210 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1040209 y x z) (@lem0)). Qed.
Lemma lem1040211 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1040210 y x z) (@lem1039865 x y z)). Qed.
Lemma lem1040213 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1040214 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1040213 (term315 y x z) (y = z)). Qed.
Lemma lem1040216 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1040217 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1040216 (term260 x y) (term260 x z)). Qed.
Lemma lem1040219 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1040220 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1040219 (x = y)). Qed.
Lemma lem1040221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1040222 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1040221) (@lem1040220 x y)). Qed.
Lemma lem1040224 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1040225 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1040224 (x = z)). Qed.
Lemma lem1040226 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1040222 x y) (@lem1040225 x z)). Qed.
Lemma lem1040227 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1040217 y x z) (@lem1040226 y x z)). Qed.
Lemma lem1040228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1040229 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1040228) (@lem1040227 y x z)). Qed.
Lemma lem1040230 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1040231 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1040229 y x z) (@lem1040230 y z)). Qed.
Lemma lem1040232 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1040214 x y z) (@lem1040231 x y z)). Qed.
Lemma lem1040234 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : term444 w d' z d.
Proof. exact (conj (@lem1040113 d' w d z h1 h3) (@lem1040121 w d' z d h2)). Qed.
Lemma lem1040236 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1040232 x y z) (@lem1040211 y x z)). Qed.
Lemma lem1040237 (w : nat) (d' : nat) (z : nat) (d : nat) : term445 w d' z d.
Proof. exact (@lem1040236 (term54 d' d w z) (term58 d' w z d) (term149 w d' z d)). Qed.
Lemma lem1040240 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : (term58 d' w z d) = (term149 w d' z d).
Proof. exact (@lem1040237 w d' z d (@lem1040234 w d' d z h1 h2 h3)). Qed.
Lemma lem1040241 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : term446 w d' z d.
Proof. exact (fun h0 : term447 w d' z d => @lem1040240 w d' d z h1 h2 h3). Qed.
Lemma lem1040243 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1040244 (w : nat) (d' : nat) (z : nat) (d : nat) : (term446 w d' z d) = ((term58 d' w z d) = (term149 w d' z d)).
Proof. exact (@lem1040243 ((term58 d' w z d) = (term149 w d' z d))). Qed.
Lemma lem1040245 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : (term58 d' w z d) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1040244 w d' z d) (@lem1040241 w d' d z h1 h2 h3)). Qed.
Lemma lem1040246 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : term547 w d' z d.
Proof. exact (conj (@lem1039873 d w d' z h2) (@lem1040245 w d' d z h1 h2 h3)). Qed.
Lemma lem1040248 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1040232 x y z) (@lem1040211 y x z)). Qed.
Lemma lem1040249 (w : nat) (d' : nat) (z : nat) (d : nat) : term548 w d' z d.
Proof. exact (@lem1040248 (term58 d' w z d) (term150 d w d' z) (term149 w d' z d)). Qed.
Lemma lem1040252 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (@lem1040249 w d' z d (@lem1040246 w d' d z h1 h2 h3)). Qed.
Lemma lem1040253 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : term539 w d' z d.
Proof. exact (fun h0 : term537 w d' z d => @lem1040252 w d' d z h1 h2 h3). Qed.
Lemma lem1040255 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1040256 (w : nat) (d' : nat) (z : nat) (d : nat) : (term539 w d' z d) = ((term150 d w d' z) = (term149 w d' z d)).
Proof. exact (@lem1040255 ((term150 d w d' z) = (term149 w d' z d))). Qed.
Lemma lem1040257 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : (Nat.add z d) = z) : (term150 d w d' z) = (term149 w d' z d).
Proof. exact (EQ_MP (@lem1040256 w d' z d) (@lem1040253 w d' d z h1 h2 h3)). Qed.
Lemma lem1040260 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1040262 (w : nat) (d' : nat) (z : nat) (d : nat) : (term537 w d' z d) = (term549 w d' z d).
Proof. exact (@lem1040260 ((term150 d w d' z) = (term149 w d' z d))). Qed.
Lemma lem1040265 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term528 w d' d z) : term549 w d' z d.
Proof. exact (EQ_MP (@lem1040262 w d' z d) (@lem1038576 w d' d z h1)). Qed.
Lemma lem1040268 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (@lem1040265 w d' d z h3 (@lem1040257 w d' d z h1 h2 h4)). Qed.
Lemma lem1040269 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : term410.
Proof. exact (fun h0 : ~ False => @lem1040268 w d' d z h1 h2 h3 h4). Qed.
Lemma lem1040271 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1040272 : term410 = False.
Proof. exact (@lem1040271 False). Qed.
Lemma lem1040273 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1040272) (@lem1040269 w d' d z h1 h2 h3 h4)). Qed.
Lemma lem1040274 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h5 : (Nat.add z d) = z => @lem1040273 w d' d z h1 h2 h3 h4) (fun h5 : False => @lem1038578 d z h4)). Qed.
Lemma lem1040275 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1040274 w d' d z h1 h2 h3 h4) (@lem1038578 d z h4)). Qed.
Lemma lem1040276 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1039833 d z w d' h1 h2 h3 h4) (fun h5 : False => @lem1038518 w d' h4)). Qed.
Lemma lem1040277 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1040276 d z w d' h1 h2 h3 h4) (@lem1038518 w d' h4)). Qed.
Lemma lem1040278 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h5 : (Nat.add z d) = z => @lem1040275 w d' d z h1 h2 h3 h4) (fun h5 : False => @lem1038346 d z h4)). Qed.
Lemma lem1040279 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1040278 w d' d z h1 h2 h3 h4) (@lem1038346 d z h4)). Qed.
Lemma lem1040280 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1040277 d z w d' h1 h2 h3 h4) (fun h5 : False => @lem1038240 w d' h4)). Qed.
Lemma lem1040281 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1040280 d z w d' h1 h2 h3 h4) (@lem1038240 w d' h4)). Qed.
Lemma lem1040282 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h5 : (Nat.add z d) = z => @lem1040279 w d' d z h1 h2 h3 h4) (fun h5 : False => @lem1038346 d z h4)). Qed.
Lemma lem1040283 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1040282 w d' d z h1 h2 h3 h4) (@lem1038346 d z h4)). Qed.
Lemma lem1040284 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : term216 = False.
Proof. exact (prop_ext (fun h5 : term216 => @lem1040283 w d' d z h1 h2 h3 h4) (fun h5 : False => @lem1038260 h2)). Qed.
Lemma lem1040285 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1040284 w d' d z h1 h2 h3 h4) (@lem1038260 h2)). Qed.
Lemma lem1040286 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : (w = (Nat.add w d')) = False.
Proof. exact (prop_ext (fun h5 : w = (Nat.add w d') => @lem1040281 d z w d' h1 h2 h3 h4) (fun h5 : False => @lem1038240 w d' h4)). Qed.
Lemma lem1040287 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1040286 d z w d' h1 h2 h3 h4) (@lem1038240 w d' h4)). Qed.
Lemma lem1040288 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : term216 = False.
Proof. exact (prop_ext (fun h5 : term216 => @lem1040287 d z w d' h1 h2 h3 h4) (fun h5 : False => @lem1038154 h2)). Qed.
Lemma lem1040289 (d : nat) (z : nat) (w : nat) (d' : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) (h4 : w = (Nat.add w d')) : False.
Proof. exact (EQ_MP (@lem1040288 d z w d' h1 h2 h3 h4) (@lem1038154 h2)). Qed.
Lemma lem1040290 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1039338 w d' d z h1 h2 h3) (fun h4 : False => @lem1038044 h2)). Qed.
Lemma lem1040291 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term531 w d' d z) : False.
Proof. exact (EQ_MP (@lem1040290 w d' d z h1 h2 h3) (@lem1038044 h2)). Qed.
Lemma lem1040292 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term528 w d' d z) : False.
Proof. exact (or_elim (@lem1038021 w d' d z h3) (fun h0 : w = (Nat.add w d') => @lem1040289 d z w d' h1 h2 h3 h0) (fun h0 : (Nat.add z d) = z => @lem1040285 w d' d z h1 h2 h3 h0)). Qed.
Lemma lem1040293 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term503 w d' d z) : False.
Proof. exact (or_elim (@lem1037828 w d' d z h3) (fun h0 : term531 w d' d z => @lem1040291 w d' d z h1 h2 h0) (fun h0 : term528 w d' d z => @lem1040292 w d' d z h1 h2 h0)). Qed.
Lemma lem1040294 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term503 w d' d z) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1040293 w d' d z h1 h2 h3) (fun h4 : False => @lem1037868 h2)). Qed.
Lemma lem1040295 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term503 w d' d z) : False.
Proof. exact (EQ_MP (@lem1040294 w d' d z h1 h2 h3) (@lem1037868 h2)). Qed.
Lemma lem1040296 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term503 w d' d z) : term216 = False.
Proof. exact (prop_ext (fun h4 : term216 => @lem1040295 w d' d z h1 h2 h3) (fun h4 : False => @lem1037552 h2)). Qed.
Lemma lem1040297 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term216) (h3 : term503 w d' d z) : False.
Proof. exact (EQ_MP (@lem1040296 w d' d z h1 h2 h3) (@lem1037552 h2)). Qed.
Lemma lem1040298 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term503 w d' d z) : term181.
Proof. exact (fun h0 : term107 => @lem1040297 w d' d z h0 h1 h2). Qed.
Lemma lem1040299 : term181 = term182.
Proof. exact (@lem69 term107). Qed.
Lemma lem1040300 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term216) (h2 : term503 w d' d z) : term182.
Proof. exact (EQ_MP (@lem1040299) (@lem1040298 w d' d z h1 h2)). Qed.
Lemma lem1040301 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term185.
Proof. exact (fun h0 : term216 => @lem1040300 w d' d z h0 h1). Qed.
Lemma lem1040302 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term188.
Proof. exact (fun h0 : term220 => @lem1040301 w d' d z h1). Qed.
Lemma lem1040303 (w : nat) (d' : nat) (d : nat) (z : nat) : term509 w d' d z.
Proof. exact (fun h0 : term503 w d' d z => @lem1040302 w d' d z h0). Qed.
Lemma lem1040308 (d' : nat) (d : nat) (z : nat) : term513 d' d z.
Proof. exact (fun w : nat => @lem1040303 w d' d z). Qed.
Lemma lem1040313 (d : nat) (z : nat) : term517 d z.
Proof. exact (fun d' : nat => @lem1040308 d' d z). Qed.
Lemma lem1040318 (z : nat) : term521 z.
Proof. exact (fun d : nat => @lem1040313 d z). Qed.
Lemma lem1040323 : term525.
Proof. exact (fun z : nat => @lem1040318 z). Qed.
Lemma lem1040324 : term524.
Proof. exact (EQ_MP (@lem1037478) (@lem1040323)). Qed.
Lemma lem1040325 (z : nat) : term575 z.
Proof. exact (@lem1040324 z). Qed.
Lemma lem1040326 (z : nat) : (term575 z) = (term520 z).
Proof. exact (eq_refl (term575 z)). Qed.
Lemma lem1040327 (z : nat) : term520 z.
Proof. exact (EQ_MP (@lem1040326 z) (@lem1040325 z)). Qed.
Lemma lem1040328 (z : nat) (d : nat) : term576 z d.
Proof. exact (@lem1040327 z d). Qed.
Lemma lem1040329 (d : nat) (z : nat) : (term576 z d) = (term516 d z).
Proof. exact (eq_refl (term576 z d)). Qed.
Lemma lem1040330 (d : nat) (z : nat) : term516 d z.
Proof. exact (EQ_MP (@lem1040329 d z) (@lem1040328 z d)). Qed.
Lemma lem1040331 (d : nat) (z : nat) (d' : nat) : term577 d z d'.
Proof. exact (@lem1040330 d z d'). Qed.
Lemma lem1040332 (d' : nat) (d : nat) (z : nat) : (term577 d z d') = (term512 d' d z).
Proof. exact (eq_refl (term577 d z d')). Qed.
Lemma lem1040333 (d' : nat) (d : nat) (z : nat) : term512 d' d z.
Proof. exact (EQ_MP (@lem1040332 d' d z) (@lem1040331 d z d')). Qed.
Lemma lem1040334 (d' : nat) (d : nat) (z : nat) (w : nat) : term578 d' d z w.
Proof. exact (@lem1040333 d' d z w). Qed.
Lemma lem1040335 (w : nat) (d' : nat) (d : nat) (z : nat) : (term578 d' d z w) = (term504 w d' d z).
Proof. exact (eq_refl (term578 d' d z w)). Qed.
Lemma lem1040336 (w : nat) (d' : nat) (d : nat) (z : nat) : term504 w d' d z.
Proof. exact (EQ_MP (@lem1040335 w d' d z) (@lem1040334 d' d z w)). Qed.
Lemma lem1040338 (w : nat) (d' : nat) (d : nat) (z : nat) : term504 w d' d z.
Proof. exact (@lem1037176 w d' d z (@lem1040336 w d' d z)). Qed.
Lemma lem1040339 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term187.
Proof. exact (@lem1040338 w d' d z (@lem1037161 w d' d z h1)). Qed.
Lemma lem1040340 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term184.
Proof. exact (@lem1040339 w d' d z h1 (@lem81820)). Qed.
Lemma lem1040341 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : term181.
Proof. exact (@lem1040340 w d' d z h1 (@lem77775)). Qed.
Lemma lem1040342 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : False.
Proof. exact (@lem1040341 w d' d z h1 (@lem1033477)). Qed.
Lemma lem1040343 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : (term503 w d' d z) = False.
Proof. exact (prop_ext (fun h2 : term503 w d' d z => @lem1040342 w d' d z h1) (fun h2 : False => @lem1037161 w d' d z h1)). Qed.
Lemma lem1040344 (w : nat) (d' : nat) (d : nat) (z : nat) (h1 : term503 w d' d z) : False.
Proof. exact (EQ_MP (@lem1040343 w d' d z h1) (@lem1037161 w d' d z h1)). Qed.
Lemma lem1040345 (w : nat) (d' : nat) (d : nat) (z : nat) : term502 w d' d z.
Proof. exact (fun h0 : term503 w d' d z => @lem1040344 w d' d z h0). Qed.
Lemma lem1040346 (w : nat) (d' : nat) (d : nat) (z : nat) : ((term150 d w d' z) = (term149 w d' z d)) = (term162 w d' d z).
Proof. exact (EQ_MP (@lem1037160 w d' d z) (@lem1040345 w d' d z)). Qed.
Lemma lem1040348 (p : Prop) : p = (term174 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1040349 (d' : nat) (x : nat) (y : nat) (d : nat) : (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)) = (term579 d' x y d).
Proof. exact (@lem1040348 (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d))). Qed.
Lemma lem1040350 (d' : nat) (x : nat) (y : nat) (d : nat) : (term579 d' x y d) = (((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d)).
Proof. exact (SYM (@lem1040349 d' x y d)). Qed.
Lemma lem1040351 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term580 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040354 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term581 d' x y d) : term581 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040355 (d' : nat) (x : nat) (y : nat) (d : nat) : term582 d' x y d.
Proof. exact (fun h0 : term581 d' x y d => @lem1040354 d' x y d h0). Qed.
Lemma lem1040356 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term582 d' x y d) : term582 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040357 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term581 d' x y d) : term581 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040358 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term581 d' x y d) (h2 : term582 d' x y d) : term581 d' x y d.
Proof. exact (@lem1040356 d' x y d h2 (@lem1040357 d' x y d h1)). Qed.
Lemma lem1040359 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term581 d' x y d) : term583 d' x y d.
Proof. exact (fun h0 : term582 d' x y d => @lem1040358 d' x y d h1 h0). Qed.
Lemma lem1040360 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term582 d' x y d) : term582 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040361 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term581 d' x y d) (h2 : term582 d' x y d) : term581 d' x y d.
Proof. exact (@lem1040359 d' x y d h1 (@lem1040360 d' x y d h2)). Qed.
Lemma lem1040362 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term582 d' x y d) : term582 d' x y d.
Proof. exact (fun h0 : term581 d' x y d => @lem1040361 d' x y d h0 h1). Qed.
Lemma lem1040363 (d' : nat) (x : nat) (y : nat) (d : nat) : term584 d' x y d.
Proof. exact (fun h0 : term582 d' x y d => @lem1040362 d' x y d h0). Qed.
Lemma lem1040366 (d' : nat) (x : nat) (y : nat) (d : nat) : term582 d' x y d.
Proof. exact (@lem1040363 d' x y d (@lem1040355 d' x y d)). Qed.
Lemma lem1040408 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1040409 : term181 = term182.
Proof. exact (@lem1040408 term107). Qed.
Lemma lem1040440 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1040441 : term184 = term185.
Proof. exact (MK_COMB (@lem1040440) (@lem1040409)). Qed.
Lemma lem1040444 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem1040445 : term187 = term188.
Proof. exact (MK_COMB (@lem1040444) (@lem1040441)). Qed.
Lemma lem1040448 (d' : nat) (x : nat) (y : nat) (d : nat) : (term585 d' x y d) = (term585 d' x y d).
Proof. exact (eq_refl (term585 d' x y d)). Qed.
Lemma lem1040449 (d' : nat) (x : nat) (y : nat) (d : nat) : (term581 d' x y d) = (term586 d' x y d).
Proof. exact (MK_COMB (@lem1040448 d' x y d) (@lem1040445)). Qed.
Lemma lem1040452 (x : nat) (y : nat) (d : nat) : (term587 x y d) = (term588 x y d).
Proof. exact (fun_ext (fun d' : nat => @lem1040449 d' x y d)). Qed.
Lemma lem1040453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040454 (x : nat) (y : nat) (d : nat) : (term589 x y d) = (term590 x y d).
Proof. exact (MK_COMB (@lem1040453) (@lem1040452 x y d)). Qed.
Lemma lem1040459 (y : nat) (d : nat) : (term591 y d) = (term592 y d).
Proof. exact (fun_ext (fun x : nat => @lem1040454 x y d)). Qed.
Lemma lem1040460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040461 (y : nat) (d : nat) : (term593 y d) = (term594 y d).
Proof. exact (MK_COMB (@lem1040460) (@lem1040459 y d)). Qed.
Lemma lem1040466 (d : nat) : (term595 d) = (term596 d).
Proof. exact (fun_ext (fun y : nat => @lem1040461 y d)). Qed.
Lemma lem1040467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040468 (d : nat) : (term597 d) = (term598 d).
Proof. exact (MK_COMB (@lem1040467) (@lem1040466 d)). Qed.
Lemma lem1040473 : term599 = term600.
Proof. exact (fun_ext (fun d : nat => @lem1040468 d)). Qed.
Lemma lem1040474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040483 : term601 = term602.
Proof. exact (MK_COMB (@lem1040474) (@lem1040473)). Qed.
Lemma lem1040500 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term94 d e w x y z).
Proof. exact (eq_refl (term94 d e w x y z)). Qed.
Lemma lem1040501 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term207 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1040500 d e w x y z)). Qed.
Lemma lem1040502 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040503 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term102 d e w x y).
Proof. exact (MK_COMB (@lem1040502) (@lem1040501 d e w x y)). Qed.
Lemma lem1040504 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term208 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1040503 d e w x y)). Qed.
Lemma lem1040505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040506 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term103 d e w x).
Proof. exact (MK_COMB (@lem1040505) (@lem1040504 d e w x)). Qed.
Lemma lem1040507 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term209 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1040506 d e w x)). Qed.
Lemma lem1040508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040509 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term104 d e w).
Proof. exact (MK_COMB (@lem1040508) (@lem1040507 d e w)). Qed.
Lemma lem1040510 (d : nat) (e : nat) : (term210 d e) = (term210 d e).
Proof. exact (fun_ext (fun w : nat => @lem1040509 d e w)). Qed.
Lemma lem1040511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040512 (d : nat) (e : nat) : (term105 d e) = (term105 d e).
Proof. exact (MK_COMB (@lem1040511) (@lem1040510 d e)). Qed.
Lemma lem1040513 (d : nat) : (term211 d) = (term211 d).
Proof. exact (fun_ext (fun e : nat => @lem1040512 d e)). Qed.
Lemma lem1040514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040515 (d : nat) : (term106 d) = (term106 d).
Proof. exact (MK_COMB (@lem1040514) (@lem1040513 d)). Qed.
Lemma lem1040516 : term212 = term212.
Proof. exact (fun_ext (fun d : nat => @lem1040515 d)). Qed.
Lemma lem1040517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040518 : term107 = term107.
Proof. exact (MK_COMB (@lem1040517) (@lem1040516)). Qed.
Lemma lem1040519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1040520 : term182 = term182.
Proof. exact (MK_COMB (@lem1040519) (@lem1040518)). Qed.
Lemma lem1040521 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1040522 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1040521 n m)). Qed.
Lemma lem1040523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040524 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1040523) (@lem1040522 m)). Qed.
Lemma lem1040525 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1040524 m)). Qed.
Lemma lem1040526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040527 : term216 = term216.
Proof. exact (MK_COMB (@lem1040526) (@lem1040525)). Qed.
Lemma lem1040528 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1040529 : term183 = term183.
Proof. exact (MK_COMB (@lem1040528) (@lem1040527)). Qed.
Lemma lem1040530 : term185 = term185.
Proof. exact (MK_COMB (@lem1040529) (@lem1040520)). Qed.
Lemma lem1040531 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1040532 (m : nat) : (term217 m) = (term217 m).
Proof. exact (fun_ext (fun n : nat => @lem1040531 n m)). Qed.
Lemma lem1040533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040534 (m : nat) : (term218 m) = (term218 m).
Proof. exact (MK_COMB (@lem1040533) (@lem1040532 m)). Qed.
Lemma lem1040535 : term219 = term219.
Proof. exact (fun_ext (fun m : nat => @lem1040534 m)). Qed.
Lemma lem1040536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040537 : term220 = term220.
Proof. exact (MK_COMB (@lem1040536) (@lem1040535)). Qed.
Lemma lem1040538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1040539 : term186 = term186.
Proof. exact (MK_COMB (@lem1040538) (@lem1040537)). Qed.
Lemma lem1040540 : term188 = term188.
Proof. exact (MK_COMB (@lem1040539) (@lem1040530)). Qed.
Lemma lem1040553 (d' : nat) (x : nat) (y : nat) (d : nat) : (term585 d' x y d) = (term585 d' x y d).
Proof. exact (eq_refl (term585 d' x y d)). Qed.
Lemma lem1040554 (d' : nat) (x : nat) (y : nat) (d : nat) : (term586 d' x y d) = (term586 d' x y d).
Proof. exact (MK_COMB (@lem1040553 d' x y d) (@lem1040540)). Qed.
Lemma lem1040555 (x : nat) (y : nat) (d : nat) : (term588 x y d) = (term588 x y d).
Proof. exact (fun_ext (fun d' : nat => @lem1040554 d' x y d)). Qed.
Lemma lem1040556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040557 (x : nat) (y : nat) (d : nat) : (term590 x y d) = (term590 x y d).
Proof. exact (MK_COMB (@lem1040556) (@lem1040555 x y d)). Qed.
Lemma lem1040558 (y : nat) (d : nat) : (term592 y d) = (term592 y d).
Proof. exact (fun_ext (fun x : nat => @lem1040557 x y d)). Qed.
Lemma lem1040559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040560 (y : nat) (d : nat) : (term594 y d) = (term594 y d).
Proof. exact (MK_COMB (@lem1040559) (@lem1040558 y d)). Qed.
Lemma lem1040561 (d : nat) : (term596 d) = (term596 d).
Proof. exact (fun_ext (fun y : nat => @lem1040560 y d)). Qed.
Lemma lem1040562 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040563 (d : nat) : (term598 d) = (term598 d).
Proof. exact (MK_COMB (@lem1040562) (@lem1040561 d)). Qed.
Lemma lem1040564 : term600 = term600.
Proof. exact (fun_ext (fun d : nat => @lem1040563 d)). Qed.
Lemma lem1040565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040566 : term602 = term602.
Proof. exact (MK_COMB (@lem1040565) (@lem1040564)). Qed.
Lemma lem1040667 : term601 = term602.
Proof. exact (TRANS (@lem1040483) (@lem1040566)). Qed.
Lemma lem1040668 : term602 = term601.
Proof. exact (SYM (@lem1040667)). Qed.
Lemma lem1040669 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term580 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1040672 (h1 : term107) : term107.
Proof. exact (h1). Qed.
Lemma lem1040683 (d' : nat) (x : nat) (y : nat) (d : nat) : (term603 d' x y d) = (term604 d' x y d).
Proof. exact (@lem17160 ((Nat.add x d') = x) (y = (Nat.add y d))). Qed.
Lemma lem1040689 (d' : nat) (x : nat) (y : nat) (d : nat) : (term605 d' x y d) = (term605 d' x y d).
Proof. exact (eq_refl (term605 d' x y d)). Qed.
Lemma lem1040691 (d' : nat) (d : nat) (x : nat) (y : nat) : (term606 d' d x y) = (term606 d' d x y).
Proof. exact (eq_refl (term606 d' d x y)). Qed.
Lemma lem1040692 (d' : nat) (x : nat) (y : nat) (d : nat) : (term607 d' x y d) = (term608 d' x y d).
Proof. exact (MK_COMB (@lem1040691 d' d x y) (@lem1040683 d' x y d)). Qed.
Lemma lem1040693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1040694 (d' : nat) (x : nat) (y : nat) (d : nat) : (term609 d' x y d) = (term610 d' x y d).
Proof. exact (MK_COMB (@lem1040693) (@lem1040692 d' x y d)). Qed.
Lemma lem1040695 (d' : nat) (x : nat) (y : nat) (d : nat) : (term611 d' x y d) = (term612 d' x y d).
Proof. exact (MK_COMB (@lem1040694 d' x y d) (@lem1040689 d' x y d)). Qed.
Lemma lem1040696 (d' : nat) (x : nat) (y : nat) (d : nat) : (term580 d' x y d) = (term611 d' x y d).
Proof. exact (@lem17646 ((term58 d' x y d) = (term54 d' d x y)) (term168 d' x y d)). Qed.
Lemma lem1040701 (d' : nat) (x : nat) (y : nat) (d : nat) : (term580 d' x y d) = (term612 d' x y d).
Proof. exact (TRANS (@lem1040696 d' x y d) (@lem1040695 d' x y d)). Qed.
Lemma lem1040749 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term231 w x d y z e) = (term232 w x d y z e).
Proof. exact (@lem17045 (w = (Nat.add x d)) (y = (Nat.add z e))). Qed.
Lemma lem1040760 (w : nat) (x : nat) (y : nat) (z : nat) : (term233 w x y z) = (term234 w x y z).
Proof. exact (@lem17160 (w = x) (y = z)). Qed.
Lemma lem1040766 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1040768 (w : nat) (z : nat) (x : nat) (y : nat) : (term236 w z x y) = (term236 w z x y).
Proof. exact (eq_refl (term236 w z x y)). Qed.
Lemma lem1040769 (w : nat) (x : nat) (y : nat) (z : nat) : (term237 w x y z) = (term238 w x y z).
Proof. exact (MK_COMB (@lem1040768 w z x y) (@lem1040760 w x y z)). Qed.
Lemma lem1040770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1040771 (w : nat) (x : nat) (y : nat) (z : nat) : (term239 w x y z) = (term240 w x y z).
Proof. exact (MK_COMB (@lem1040770) (@lem1040769 w x y z)). Qed.
Lemma lem1040772 (w : nat) (x : nat) (y : nat) (z : nat) : (term241 w x y z) = (term242 w x y z).
Proof. exact (MK_COMB (@lem1040771 w x y z) (@lem1040766 w x y z)). Qed.
Lemma lem1040773 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term241 w x y z).
Proof. exact (@lem17784 ((term53 w y x z) = (term53 w z x y)) (term64 w x y z)). Qed.
Lemma lem1040774 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term242 w x y z).
Proof. exact (TRANS (@lem1040773 w x y z) (@lem1040772 w x y z)). Qed.
Lemma lem1040775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1040776 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term243 w x d y z e) = (term244 w x d y z e).
Proof. exact (MK_COMB (@lem1040775) (@lem1040749 w x d y z e)). Qed.
Lemma lem1040777 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term245 d e w x y z) = (term246 d e w x y z).
Proof. exact (MK_COMB (@lem1040776 w x d y z e) (@lem1040774 w x y z)). Qed.
Lemma lem1040778 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term245 d e w x y z).
Proof. exact (@lem17265 (term48 w x d y z e) (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z))). Qed.
Lemma lem1040779 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term246 d e w x y z).
Proof. exact (TRANS (@lem1040778 d e w x y z) (@lem1040777 d e w x y z)). Qed.
Lemma lem1040780 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1040779 d e w x y z)). Qed.
Lemma lem1040781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040782 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1040781) (@lem1040780 d e w x y)). Qed.
Lemma lem1040783 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1040782 d e w x y)). Qed.
Lemma lem1040784 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040785 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1040784) (@lem1040783 d e w x)). Qed.
Lemma lem1040786 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1040785 d e w x)). Qed.
Lemma lem1040787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040788 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1040787) (@lem1040786 d e w)). Qed.
Lemma lem1040789 (d : nat) (e : nat) : (term210 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1040788 d e w)). Qed.
Lemma lem1040790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040791 (d : nat) (e : nat) : (term105 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1040790) (@lem1040789 d e)). Qed.
Lemma lem1040792 (d : nat) : (term211 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1040791 d e)). Qed.
Lemma lem1040793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040794 (d : nat) : (term106 d) = (term256 d).
Proof. exact (MK_COMB (@lem1040793) (@lem1040792 d)). Qed.
Lemma lem1040795 : term212 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1040794 d)). Qed.
Lemma lem1040796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1040869 : term107 = term258.
Proof. exact (MK_COMB (@lem1040796) (@lem1040795)). Qed.
Lemma lem1040870 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1040869) (@lem1040672 h1)). Qed.
Lemma lem1041018 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term612 d' x y d.
Proof. exact (EQ_MP (@lem1040701 d' x y d) (@lem1040669 d' x y d h1)). Qed.
Lemma lem1041185 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term246 d e w x y z).
Proof. exact (eq_refl (term246 d e w x y z)). Qed.
Lemma lem1041186 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1041185 d e w x y z)). Qed.
Lemma lem1041187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041188 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1041187) (@lem1041186 d e w x y)). Qed.
Lemma lem1041189 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1041188 d e w x y)). Qed.
Lemma lem1041190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041191 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1041190) (@lem1041189 d e w x)). Qed.
Lemma lem1041192 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1041191 d e w x)). Qed.
Lemma lem1041193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041194 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1041193) (@lem1041192 d e w)). Qed.
Lemma lem1041195 (d : nat) (e : nat) : (term253 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1041194 d e w)). Qed.
Lemma lem1041196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041197 (d : nat) (e : nat) : (term254 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1041196) (@lem1041195 d e)). Qed.
Lemma lem1041198 (d : nat) : (term255 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1041197 d e)). Qed.
Lemma lem1041199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041200 (d : nat) : (term256 d) = (term256 d).
Proof. exact (MK_COMB (@lem1041199) (@lem1041198 d)). Qed.
Lemma lem1041201 : term257 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1041200 d)). Qed.
Lemma lem1041202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041203 : term258 = term258.
Proof. exact (MK_COMB (@lem1041202) (@lem1041201)). Qed.
Lemma lem1041204 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1041203) (@lem1040870 h1)). Qed.
Lemma lem1041205 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term608 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1041206 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term605 d' x y d.
Proof. exact (h1). Qed.
Lemma lem1041207 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term604 d' x y d.
Proof. exact (proj2 (@lem1041205 d' x y d h1)). Qed.
Lemma lem1041211 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term168 d' x y d.
Proof. exact (proj2 (@lem1041206 d' x y d h1)). Qed.
Lemma lem1041248 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1041265 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1041266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041267 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1041266) (@lem1041265 w x y z)). Qed.
Lemma lem1041268 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1041267 w x y z) (@lem1041248 w x y z)). Qed.
Lemma lem1041277 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1041278 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1041277 w x d y z e) (@lem1041268 w x y z)). Qed.
Lemma lem1041279 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1041280 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1041287 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1041288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041289 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1041288) (@lem1041287 d e w x y z)). Qed.
Lemma lem1041290 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1041289 d e w x y z) (@lem1041280 d e w x y z)). Qed.
Lemma lem1041291 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041279 d e w x y z) (@lem1041290 d e w x y z)). Qed.
Lemma lem1041292 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041278 d e w x y z) (@lem1041291 d e w x y z)). Qed.
Lemma lem1041293 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1041292 d e w x y z)). Qed.
Lemma lem1041294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041295 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1041294) (@lem1041293 d e w x y)). Qed.
Lemma lem1041296 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1041295 d e w x y)). Qed.
Lemma lem1041297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041298 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1041297) (@lem1041296 d e w x)). Qed.
Lemma lem1041299 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1041298 d e w x)). Qed.
Lemma lem1041300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041301 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1041300) (@lem1041299 d e w)). Qed.
Lemma lem1041302 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1041301 d e w)). Qed.
Lemma lem1041303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041304 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1041303) (@lem1041302 d e)). Qed.
Lemma lem1041305 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1041304 d e)). Qed.
Lemma lem1041306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041307 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1041306) (@lem1041305 d)). Qed.
Lemma lem1041308 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1041307 d)). Qed.
Lemma lem1041309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041311 : term258 = term284.
Proof. exact (MK_COMB (@lem1041309) (@lem1041308)). Qed.
Lemma lem1041312 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1041311) (@lem1041204 h1)). Qed.
Lemma lem1041358 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1041375 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1041376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041377 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1041376) (@lem1041375 w x y z)). Qed.
Lemma lem1041378 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1041377 w x y z) (@lem1041358 w x y z)). Qed.
Lemma lem1041387 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1041388 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1041387 w x d y z e) (@lem1041378 w x y z)). Qed.
Lemma lem1041389 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1041390 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1041397 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1041398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041399 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1041398) (@lem1041397 d e w x y z)). Qed.
Lemma lem1041400 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1041399 d e w x y z) (@lem1041390 d e w x y z)). Qed.
Lemma lem1041401 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041389 d e w x y z) (@lem1041400 d e w x y z)). Qed.
Lemma lem1041402 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041388 d e w x y z) (@lem1041401 d e w x y z)). Qed.
Lemma lem1041403 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1041402 d e w x y z)). Qed.
Lemma lem1041404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041405 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1041404) (@lem1041403 d e w x y)). Qed.
Lemma lem1041406 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1041405 d e w x y)). Qed.
Lemma lem1041407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041408 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1041407) (@lem1041406 d e w x)). Qed.
Lemma lem1041409 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1041408 d e w x)). Qed.
Lemma lem1041410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041411 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1041410) (@lem1041409 d e w)). Qed.
Lemma lem1041412 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1041411 d e w)). Qed.
Lemma lem1041413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041414 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1041413) (@lem1041412 d e)). Qed.
Lemma lem1041415 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1041414 d e)). Qed.
Lemma lem1041416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041417 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1041416) (@lem1041415 d)). Qed.
Lemma lem1041418 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1041417 d)). Qed.
Lemma lem1041419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041421 : term258 = term284.
Proof. exact (MK_COMB (@lem1041419) (@lem1041418)). Qed.
Lemma lem1041422 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1041421) (@lem1041204 h1)). Qed.
Lemma lem1041430 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1041464 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1041481 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1041482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041483 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1041482) (@lem1041481 w x y z)). Qed.
Lemma lem1041484 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1041483 w x y z) (@lem1041464 w x y z)). Qed.
Lemma lem1041493 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1041494 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1041493 w x d y z e) (@lem1041484 w x y z)). Qed.
Lemma lem1041495 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1041496 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1041503 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1041504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041505 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1041504) (@lem1041503 d e w x y z)). Qed.
Lemma lem1041506 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1041505 d e w x y z) (@lem1041496 d e w x y z)). Qed.
Lemma lem1041507 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041495 d e w x y z) (@lem1041506 d e w x y z)). Qed.
Lemma lem1041508 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1041494 d e w x y z) (@lem1041507 d e w x y z)). Qed.
Lemma lem1041509 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1041508 d e w x y z)). Qed.
Lemma lem1041510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041511 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1041510) (@lem1041509 d e w x y)). Qed.
Lemma lem1041512 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1041511 d e w x y)). Qed.
Lemma lem1041513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041514 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1041513) (@lem1041512 d e w x)). Qed.
Lemma lem1041515 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1041514 d e w x)). Qed.
Lemma lem1041516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041517 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1041516) (@lem1041515 d e w)). Qed.
Lemma lem1041518 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1041517 d e w)). Qed.
Lemma lem1041519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041520 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1041519) (@lem1041518 d e)). Qed.
Lemma lem1041521 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1041520 d e)). Qed.
Lemma lem1041522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041523 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1041522) (@lem1041521 d)). Qed.
Lemma lem1041524 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1041523 d)). Qed.
Lemma lem1041525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1041527 : term258 = term284.
Proof. exact (MK_COMB (@lem1041525) (@lem1041524)). Qed.
Lemma lem1041528 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1041527) (@lem1041204 h1)). Qed.
Lemma lem1041536 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1041549 (_17216 : nat) (h1 : term107) : term287 _17216.
Proof. exact (@lem1041312 h1 _17216). Qed.
Lemma lem1041550 (_17216 : nat) : (term287 _17216) = (term282 _17216).
Proof. exact (eq_refl (term287 _17216)). Qed.
Lemma lem1041551 (_17216 : nat) (h1 : term107) : term282 _17216.
Proof. exact (EQ_MP (@lem1041550 _17216) (@lem1041549 _17216 h1)). Qed.
Lemma lem1041552 (_17216 : nat) (_17217 : nat) (h1 : term107) : term288 _17216 _17217.
Proof. exact (@lem1041551 _17216 h1 _17217). Qed.
Lemma lem1041553 (_17216 : nat) (_17217 : nat) : (term288 _17216 _17217) = (term280 _17216 _17217).
Proof. exact (eq_refl (term288 _17216 _17217)). Qed.
Lemma lem1041554 (_17216 : nat) (_17217 : nat) (h1 : term107) : term280 _17216 _17217.
Proof. exact (EQ_MP (@lem1041553 _17216 _17217) (@lem1041552 _17216 _17217 h1)). Qed.
Lemma lem1041555 (_17216 : nat) (_17217 : nat) (_17218 : nat) (h1 : term107) : term289 _17216 _17217 _17218.
Proof. exact (@lem1041554 _17216 _17217 h1 _17218). Qed.
Lemma lem1041556 (_17216 : nat) (_17217 : nat) (_17218 : nat) : (term289 _17216 _17217 _17218) = (term278 _17216 _17217 _17218).
Proof. exact (eq_refl (term289 _17216 _17217 _17218)). Qed.
Lemma lem1041557 (_17216 : nat) (_17217 : nat) (_17218 : nat) (h1 : term107) : term278 _17216 _17217 _17218.
Proof. exact (EQ_MP (@lem1041556 _17216 _17217 _17218) (@lem1041555 _17216 _17217 _17218 h1)). Qed.
Lemma lem1041558 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (h1 : term107) : term290 _17216 _17217 _17218 _17219.
Proof. exact (@lem1041557 _17216 _17217 _17218 h1 _17219). Qed.
Lemma lem1041559 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) : (term290 _17216 _17217 _17218 _17219) = (term276 _17216 _17217 _17218 _17219).
Proof. exact (eq_refl (term290 _17216 _17217 _17218 _17219)). Qed.
Lemma lem1041560 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (h1 : term107) : term276 _17216 _17217 _17218 _17219.
Proof. exact (EQ_MP (@lem1041559 _17216 _17217 _17218 _17219) (@lem1041558 _17216 _17217 _17218 _17219 h1)). Qed.
Lemma lem1041561 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (h1 : term107) : term291 _17216 _17217 _17218 _17219 _17220.
Proof. exact (@lem1041560 _17216 _17217 _17218 _17219 h1 _17220). Qed.
Lemma lem1041562 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) : (term291 _17216 _17217 _17218 _17219 _17220) = (term274 _17216 _17217 _17218 _17219 _17220).
Proof. exact (eq_refl (term291 _17216 _17217 _17218 _17219 _17220)). Qed.
Lemma lem1041563 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (h1 : term107) : term274 _17216 _17217 _17218 _17219 _17220.
Proof. exact (EQ_MP (@lem1041562 _17216 _17217 _17218 _17219 _17220) (@lem1041561 _17216 _17217 _17218 _17219 _17220 h1)). Qed.
Lemma lem1041564 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) (h1 : term107) : term292 _17216 _17217 _17218 _17219 _17220 _17221.
Proof. exact (@lem1041563 _17216 _17217 _17218 _17219 _17220 h1 _17221). Qed.
Lemma lem1041565 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term292 _17216 _17217 _17218 _17219 _17220 _17221) = (term272 _17216 _17217 _17218 _17219 _17220 _17221).
Proof. exact (eq_refl (term292 _17216 _17217 _17218 _17219 _17220 _17221)). Qed.
Lemma lem1041566 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) (h1 : term107) : term272 _17216 _17217 _17218 _17219 _17220 _17221.
Proof. exact (EQ_MP (@lem1041565 _17216 _17217 _17218 _17219 _17220 _17221) (@lem1041564 _17216 _17217 _17218 _17219 _17220 _17221 h1)). Qed.
Lemma lem1041579 (_17226 : nat) (h1 : term107) : term287 _17226.
Proof. exact (@lem1041422 h1 _17226). Qed.
Lemma lem1041580 (_17226 : nat) : (term287 _17226) = (term282 _17226).
Proof. exact (eq_refl (term287 _17226)). Qed.
Lemma lem1041581 (_17226 : nat) (h1 : term107) : term282 _17226.
Proof. exact (EQ_MP (@lem1041580 _17226) (@lem1041579 _17226 h1)). Qed.
Lemma lem1041582 (_17226 : nat) (_17227 : nat) (h1 : term107) : term288 _17226 _17227.
Proof. exact (@lem1041581 _17226 h1 _17227). Qed.
Lemma lem1041583 (_17226 : nat) (_17227 : nat) : (term288 _17226 _17227) = (term280 _17226 _17227).
Proof. exact (eq_refl (term288 _17226 _17227)). Qed.
Lemma lem1041584 (_17226 : nat) (_17227 : nat) (h1 : term107) : term280 _17226 _17227.
Proof. exact (EQ_MP (@lem1041583 _17226 _17227) (@lem1041582 _17226 _17227 h1)). Qed.
Lemma lem1041585 (_17226 : nat) (_17227 : nat) (_17228 : nat) (h1 : term107) : term289 _17226 _17227 _17228.
Proof. exact (@lem1041584 _17226 _17227 h1 _17228). Qed.
Lemma lem1041586 (_17226 : nat) (_17227 : nat) (_17228 : nat) : (term289 _17226 _17227 _17228) = (term278 _17226 _17227 _17228).
Proof. exact (eq_refl (term289 _17226 _17227 _17228)). Qed.
Lemma lem1041587 (_17226 : nat) (_17227 : nat) (_17228 : nat) (h1 : term107) : term278 _17226 _17227 _17228.
Proof. exact (EQ_MP (@lem1041586 _17226 _17227 _17228) (@lem1041585 _17226 _17227 _17228 h1)). Qed.
Lemma lem1041588 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (h1 : term107) : term290 _17226 _17227 _17228 _17229.
Proof. exact (@lem1041587 _17226 _17227 _17228 h1 _17229). Qed.
Lemma lem1041589 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term290 _17226 _17227 _17228 _17229) = (term276 _17226 _17227 _17228 _17229).
Proof. exact (eq_refl (term290 _17226 _17227 _17228 _17229)). Qed.
Lemma lem1041590 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (h1 : term107) : term276 _17226 _17227 _17228 _17229.
Proof. exact (EQ_MP (@lem1041589 _17226 _17227 _17228 _17229) (@lem1041588 _17226 _17227 _17228 _17229 h1)). Qed.
Lemma lem1041591 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (h1 : term107) : term291 _17226 _17227 _17228 _17229 _17230.
Proof. exact (@lem1041590 _17226 _17227 _17228 _17229 h1 _17230). Qed.
Lemma lem1041592 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) : (term291 _17226 _17227 _17228 _17229 _17230) = (term274 _17226 _17227 _17228 _17229 _17230).
Proof. exact (eq_refl (term291 _17226 _17227 _17228 _17229 _17230)). Qed.
Lemma lem1041593 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (h1 : term107) : term274 _17226 _17227 _17228 _17229 _17230.
Proof. exact (EQ_MP (@lem1041592 _17226 _17227 _17228 _17229 _17230) (@lem1041591 _17226 _17227 _17228 _17229 _17230 h1)). Qed.
Lemma lem1041594 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (h1 : term107) : term292 _17226 _17227 _17228 _17229 _17230 _17231.
Proof. exact (@lem1041593 _17226 _17227 _17228 _17229 _17230 h1 _17231). Qed.
Lemma lem1041595 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) : (term292 _17226 _17227 _17228 _17229 _17230 _17231) = (term272 _17226 _17227 _17228 _17229 _17230 _17231).
Proof. exact (eq_refl (term292 _17226 _17227 _17228 _17229 _17230 _17231)). Qed.
Lemma lem1041596 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (h1 : term107) : term272 _17226 _17227 _17228 _17229 _17230 _17231.
Proof. exact (EQ_MP (@lem1041595 _17226 _17227 _17228 _17229 _17230 _17231) (@lem1041594 _17226 _17227 _17228 _17229 _17230 _17231 h1)). Qed.
Lemma lem1041609 (_17236 : nat) (h1 : term107) : term287 _17236.
Proof. exact (@lem1041528 h1 _17236). Qed.
Lemma lem1041610 (_17236 : nat) : (term287 _17236) = (term282 _17236).
Proof. exact (eq_refl (term287 _17236)). Qed.
Lemma lem1041611 (_17236 : nat) (h1 : term107) : term282 _17236.
Proof. exact (EQ_MP (@lem1041610 _17236) (@lem1041609 _17236 h1)). Qed.
Lemma lem1041612 (_17236 : nat) (_17237 : nat) (h1 : term107) : term288 _17236 _17237.
Proof. exact (@lem1041611 _17236 h1 _17237). Qed.
Lemma lem1041613 (_17236 : nat) (_17237 : nat) : (term288 _17236 _17237) = (term280 _17236 _17237).
Proof. exact (eq_refl (term288 _17236 _17237)). Qed.
Lemma lem1041614 (_17236 : nat) (_17237 : nat) (h1 : term107) : term280 _17236 _17237.
Proof. exact (EQ_MP (@lem1041613 _17236 _17237) (@lem1041612 _17236 _17237 h1)). Qed.
Lemma lem1041615 (_17236 : nat) (_17237 : nat) (_17238 : nat) (h1 : term107) : term289 _17236 _17237 _17238.
Proof. exact (@lem1041614 _17236 _17237 h1 _17238). Qed.
Lemma lem1041616 (_17236 : nat) (_17237 : nat) (_17238 : nat) : (term289 _17236 _17237 _17238) = (term278 _17236 _17237 _17238).
Proof. exact (eq_refl (term289 _17236 _17237 _17238)). Qed.
Lemma lem1041617 (_17236 : nat) (_17237 : nat) (_17238 : nat) (h1 : term107) : term278 _17236 _17237 _17238.
Proof. exact (EQ_MP (@lem1041616 _17236 _17237 _17238) (@lem1041615 _17236 _17237 _17238 h1)). Qed.
Lemma lem1041618 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (h1 : term107) : term290 _17236 _17237 _17238 _17239.
Proof. exact (@lem1041617 _17236 _17237 _17238 h1 _17239). Qed.
Lemma lem1041619 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) : (term290 _17236 _17237 _17238 _17239) = (term276 _17236 _17237 _17238 _17239).
Proof. exact (eq_refl (term290 _17236 _17237 _17238 _17239)). Qed.
Lemma lem1041620 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (h1 : term107) : term276 _17236 _17237 _17238 _17239.
Proof. exact (EQ_MP (@lem1041619 _17236 _17237 _17238 _17239) (@lem1041618 _17236 _17237 _17238 _17239 h1)). Qed.
Lemma lem1041621 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (h1 : term107) : term291 _17236 _17237 _17238 _17239 _17240.
Proof. exact (@lem1041620 _17236 _17237 _17238 _17239 h1 _17240). Qed.
Lemma lem1041622 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) : (term291 _17236 _17237 _17238 _17239 _17240) = (term274 _17236 _17237 _17238 _17239 _17240).
Proof. exact (eq_refl (term291 _17236 _17237 _17238 _17239 _17240)). Qed.
Lemma lem1041623 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (h1 : term107) : term274 _17236 _17237 _17238 _17239 _17240.
Proof. exact (EQ_MP (@lem1041622 _17236 _17237 _17238 _17239 _17240) (@lem1041621 _17236 _17237 _17238 _17239 _17240 h1)). Qed.
Lemma lem1041624 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term292 _17236 _17237 _17238 _17239 _17240 _17241.
Proof. exact (@lem1041623 _17236 _17237 _17238 _17239 _17240 h1 _17241). Qed.
Lemma lem1041625 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) : (term292 _17236 _17237 _17238 _17239 _17240 _17241) = (term272 _17236 _17237 _17238 _17239 _17240 _17241).
Proof. exact (eq_refl (term292 _17236 _17237 _17238 _17239 _17240 _17241)). Qed.
Lemma lem1041626 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term272 _17236 _17237 _17238 _17239 _17240 _17241.
Proof. exact (EQ_MP (@lem1041625 _17236 _17237 _17238 _17239 _17240 _17241) (@lem1041624 _17236 _17237 _17238 _17239 _17240 _17241 h1)). Qed.
Lemma lem1041627 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) (h1 : term107) : term265 _17216 _17217 _17218 _17219 _17220 _17221.
Proof. exact (proj2 (@lem1041566 _17216 _17217 _17218 _17219 _17220 _17221 h1)). Qed.
Lemma lem1041632 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (h1 : term107) : term267 _17226 _17227 _17228 _17229 _17230 _17231.
Proof. exact (proj1 (@lem1041596 _17226 _17227 _17228 _17229 _17230 _17231 h1)). Qed.
Lemma lem1041634 (_17226 : nat) (_17227 : nat) (_17231 : nat) (_17230 : nat) (_17228 : nat) (_17229 : nat) (h1 : term107) : term293 _17226 _17227 _17231 _17230 _17228 _17229.
Proof. exact (proj1 (@lem1041632 _17226 _17227 _17228 _17229 _17230 _17231 h1)). Qed.
Lemma lem1041636 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term267 _17236 _17237 _17238 _17239 _17240 _17241.
Proof. exact (proj1 (@lem1041626 _17236 _17237 _17238 _17239 _17240 _17241 h1)). Qed.
Lemma lem1041637 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term536 _17236 _17237 _17238 _17239 _17240 _17241.
Proof. exact (proj2 (@lem1041636 _17236 _17237 _17238 _17239 _17240 _17241 h1)). Qed.
Lemma lem1041648 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term294 y d.
Proof. exact (proj2 (@lem1041207 d' x y d h1)). Qed.
Lemma lem1041667 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term265 _17216 _17217 _17218 _17219 _17220 _17221) = (term295 _17216 _17217 _17218 _17219 _17220 _17221).
Proof. exact (@lem1033471 (term296 _17218 _17219 _17216) (term296 _17220 _17221 _17217) (term235 _17218 _17219 _17220 _17221)). Qed.
Lemma lem1041668 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) (h1 : term107) : term295 _17216 _17217 _17218 _17219 _17220 _17221.
Proof. exact (EQ_MP (@lem1041667 _17216 _17217 _17218 _17219 _17220 _17221) (@lem1041627 _17216 _17217 _17218 _17219 _17220 _17221 h1)). Qed.
Lemma lem1041706 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term613 d' d x y.
Proof. exact (proj1 (@lem1041206 d' x y d h1)). Qed.
Lemma lem1041708 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1041743 (_17226 : nat) (_17227 : nat) (_17231 : nat) (_17230 : nat) (_17228 : nat) (_17229 : nat) : (term293 _17226 _17227 _17231 _17230 _17228 _17229) = (term298 _17226 _17227 _17231 _17230 _17228 _17229).
Proof. exact (@lem1033471 (term296 _17228 _17229 _17226) (term296 _17230 _17231 _17227) (term268 _17231 _17230 _17228 _17229)). Qed.
Lemma lem1041744 (_17226 : nat) (_17227 : nat) (_17231 : nat) (_17230 : nat) (_17228 : nat) (_17229 : nat) (h1 : term107) : term298 _17226 _17227 _17231 _17230 _17228 _17229.
Proof. exact (EQ_MP (@lem1041743 _17226 _17227 _17231 _17230 _17228 _17229) (@lem1041634 _17226 _17227 _17231 _17230 _17228 _17229 h1)). Qed.
Lemma lem1041766 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term613 d' d x y.
Proof. exact (proj1 (@lem1041206 d' x y d h1)). Qed.
Lemma lem1041768 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1041819 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) : (term536 _17236 _17237 _17238 _17239 _17240 _17241) = (term538 _17236 _17237 _17238 _17239 _17240 _17241).
Proof. exact (@lem1033471 (term296 _17238 _17239 _17236) (term296 _17240 _17241 _17237) (term269 _17238 _17239 _17240 _17241)). Qed.
Lemma lem1041820 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term538 _17236 _17237 _17238 _17239 _17240 _17241.
Proof. exact (EQ_MP (@lem1041819 _17236 _17237 _17238 _17239 _17240 _17241) (@lem1041637 _17236 _17237 _17238 _17239 _17240 _17241 h1)). Qed.
Lemma lem1041852 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1041854 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1041855 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1041854 (Nat.add x d')). Qed.
Lemma lem1041856 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1041855 x d'). Qed.
Lemma lem1041858 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1041859 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1041858 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1041860 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1041859 x d') (@lem1041856 x d')). Qed.
Lemma lem1041862 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1041863 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1041862 (Nat.add y d)). Qed.
Lemma lem1041864 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1041863 y d). Qed.
Lemma lem1041866 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1041867 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1041866 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1041868 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1041867 y d) (@lem1041864 y d)). Qed.
Lemma lem1041870 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (proj1 (@lem1041205 d' x y d h1)). Qed.
Lemma lem1041871 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term614 d' d x y.
Proof. exact (fun h0 : term613 d' d x y => @lem1041870 d' x y d h1). Qed.
Lemma lem1041873 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1041874 (d' : nat) (d : nat) (x : nat) (y : nat) : (term614 d' d x y) = ((term58 d' x y d) = (term54 d' d x y)).
Proof. exact (@lem1041873 ((term58 d' x y d) = (term54 d' d x y))). Qed.
Lemma lem1041875 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (EQ_MP (@lem1041874 d' d x y) (@lem1041871 d' x y d h1)). Qed.
Lemma lem1041877 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1041878 (d' : nat) (x : nat) (y : nat) (d : nat) : (term58 d' x y d) = (term58 d' x y d).
Proof. exact (@lem1041877 (term58 d' x y d)). Qed.
Lemma lem1041879 (d' : nat) (x : nat) (y : nat) (d : nat) : term615 d' x y d.
Proof. exact (fun h0 : term616 d' x y d => @lem1041878 d' x y d). Qed.
Lemma lem1041881 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1041882 (d' : nat) (x : nat) (y : nat) (d : nat) : (term615 d' x y d) = ((term58 d' x y d) = (term58 d' x y d)).
Proof. exact (@lem1041881 ((term58 d' x y d) = (term58 d' x y d))). Qed.
Lemma lem1041883 (d' : nat) (x : nat) (y : nat) (d : nat) : (term58 d' x y d) = (term58 d' x y d).
Proof. exact (EQ_MP (@lem1041882 d' x y d) (@lem1041879 d' x y d)). Qed.
Lemma lem1041901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1041902 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1041901 (y = z) (term260 x z)). Qed.
Lemma lem1041912 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1041913 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1041912 x y) (@lem1041902 y x z)). Qed.
Lemma lem1041917 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1041918 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1041917 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1041940 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1041913 y x z) (@lem1041918 y x z)). Qed.
Lemma lem1041941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1041942 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1041941) (@lem1041940 y x z)). Qed.
Lemma lem1041964 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1041965 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1041942 y x z) (@lem1041964 y x z)). Qed.
Lemma lem1041967 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1041968 (x : Prop) : (x = x) = True.
Proof. exact (@lem1041967 Prop x). Qed.
Lemma lem1041969 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1041968 (term310 y x z)). Qed.
Lemma lem1041970 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1041965 y x z) (@lem1041969 y x z)). Qed.
Lemma lem1041971 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1041970 y x z)). Qed.
Lemma lem1041972 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1041971 y x z) (@lem0)). Qed.
Lemma lem1041973 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1041972 y x z) (@lem1041852 x y z)). Qed.
Lemma lem1041975 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1041976 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1041975 (term315 y x z) (y = z)). Qed.
Lemma lem1041978 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1041979 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1041978 (term260 x y) (term260 x z)). Qed.
Lemma lem1041981 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1041982 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1041981 (x = y)). Qed.
Lemma lem1041983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1041984 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1041983) (@lem1041982 x y)). Qed.
Lemma lem1041986 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1041987 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1041986 (x = z)). Qed.
Lemma lem1041988 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1041984 x y) (@lem1041987 x z)). Qed.
Lemma lem1041989 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1041979 y x z) (@lem1041988 y x z)). Qed.
Lemma lem1041990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1041991 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1041990) (@lem1041989 y x z)). Qed.
Lemma lem1041992 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1041993 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1041991 y x z) (@lem1041992 y z)). Qed.
Lemma lem1041994 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1041976 x y z) (@lem1041993 x y z)). Qed.
Lemma lem1041996 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term617 d' x y d.
Proof. exact (conj (@lem1041875 d' x y d h1) (@lem1041883 d' x y d)). Qed.
Lemma lem1041998 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1041994 x y z) (@lem1041973 y x z)). Qed.
Lemma lem1041999 (d' : nat) (x : nat) (y : nat) (d : nat) : term618 d' x y d.
Proof. exact (@lem1041998 (term58 d' x y d) (term54 d' d x y) (term58 d' x y d)). Qed.
Lemma lem1042002 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (@lem1041999 d' x y d (@lem1041996 d' x y d h1)). Qed.
Lemma lem1042003 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term336 d' x y d.
Proof. exact (fun h0 : term337 d' x y d => @lem1042002 d' x y d h1). Qed.
Lemma lem1042005 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042006 (d' : nat) (x : nat) (y : nat) (d : nat) : (term336 d' x y d) = ((term54 d' d x y) = (term58 d' x y d)).
Proof. exact (@lem1042005 ((term54 d' d x y) = (term58 d' x y d))). Qed.
Lemma lem1042007 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (EQ_MP (@lem1042006 d' x y d) (@lem1042003 d' x y d h1)). Qed.
Lemma lem1042009 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term349 d' x.
Proof. exact (proj1 (@lem1041207 d' x y d h1)). Qed.
Lemma lem1042010 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term350 d' x.
Proof. exact (fun h0 : (Nat.add x d') = x => @lem1042009 d' x y d h1). Qed.
Lemma lem1042012 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1042013 (d' : nat) (x : nat) : (term350 d' x) = (term349 d' x).
Proof. exact (@lem1042012 ((Nat.add x d') = x)). Qed.
Lemma lem1042014 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term349 d' x.
Proof. exact (EQ_MP (@lem1042013 d' x) (@lem1042010 d' x y d h1)). Qed.
Lemma lem1042044 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042045 (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term235 _17218 _17219 _17220 _17221) = (term351 _17218 _17219 _17220 _17221).
Proof. exact (@lem1042044 (_17218 = _17219) (term352 _17218 _17221 _17219 _17220) (_17220 = _17221)). Qed.
Lemma lem1042061 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1042062 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term353 _17218 _17219 _17220 _17221) = (term354 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042061 (_17220 = _17221) (term352 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042072 (_17218 : nat) (_17219 : nat) : (term62 _17218 _17219) = (term62 _17218 _17219).
Proof. exact (eq_refl (term62 _17218 _17219)). Qed.
Lemma lem1042073 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term351 _17218 _17219 _17220 _17221) = (term355 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042072 _17218 _17219) (@lem1042062 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042084 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term235 _17218 _17219 _17220 _17221) = (term355 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042045 _17218 _17219 _17220 _17221) (@lem1042073 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042085 (_17220 : nat) (_17221 : nat) (_17217 : nat) : (term356 _17220 _17221 _17217) = (term356 _17220 _17221 _17217).
Proof. exact (eq_refl (term356 _17220 _17221 _17217)). Qed.
Lemma lem1042086 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term357 _17217 _17218 _17219 _17220 _17221) = (term358 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042085 _17220 _17221 _17217) (@lem1042084 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042090 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042091 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term358 _17217 _17218 _17221 _17219 _17220) = (term359 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042090 (_17218 = _17219) (term296 _17220 _17221 _17217) (term354 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042107 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042108 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term360 _17217 _17218 _17221 _17219 _17220) = (term361 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042107 (_17220 = _17221) (term296 _17220 _17221 _17217) (term352 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042130 (_17218 : nat) (_17219 : nat) : (term62 _17218 _17219) = (term62 _17218 _17219).
Proof. exact (eq_refl (term62 _17218 _17219)). Qed.
Lemma lem1042131 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term359 _17217 _17218 _17221 _17219 _17220) = (term362 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042130 _17218 _17219) (@lem1042108 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042142 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term358 _17217 _17218 _17221 _17219 _17220) = (term362 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042091 _17217 _17218 _17221 _17219 _17220) (@lem1042131 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042143 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term357 _17217 _17218 _17219 _17220 _17221) = (term362 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042086 _17217 _17218 _17221 _17219 _17220) (@lem1042142 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042144 (_17218 : nat) (_17219 : nat) (_17216 : nat) : (term356 _17218 _17219 _17216) = (term356 _17218 _17219 _17216).
Proof. exact (eq_refl (term356 _17218 _17219 _17216)). Qed.
Lemma lem1042145 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term363 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042144 _17218 _17219 _17216) (@lem1042143 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042149 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042150 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term363 _17216 _17217 _17218 _17221 _17219 _17220) = (term364 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042149 (_17218 = _17219) (term296 _17218 _17219 _17216) (term361 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042166 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042167 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term365 _17216 _17217 _17218 _17221 _17219 _17220) = (term366 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042166 (_17220 = _17221) (term296 _17218 _17219 _17216) (term367 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042201 (_17218 : nat) (_17219 : nat) : (term62 _17218 _17219) = (term62 _17218 _17219).
Proof. exact (eq_refl (term62 _17218 _17219)). Qed.
Lemma lem1042202 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term364 _17216 _17217 _17218 _17221 _17219 _17220) = (term368 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042201 _17218 _17219) (@lem1042167 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042213 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term363 _17216 _17217 _17218 _17221 _17219 _17220) = (term368 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042150 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042202 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042214 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term368 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042145 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042213 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1042216 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term369 _17216 _17217 _17218 _17219 _17220 _17221) = (term370 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042215) (@lem1042214 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042256 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1042257 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term371 _17221 _17220 _17218 _17219) = (term372 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042256 (_17218 = _17219) (term352 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042267 (_17220 : nat) (_17221 : nat) (_17217 : nat) : (term356 _17220 _17221 _17217) = (term356 _17220 _17221 _17217).
Proof. exact (eq_refl (term356 _17220 _17221 _17217)). Qed.
Lemma lem1042268 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term373 _17217 _17221 _17220 _17218 _17219) = (term374 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042267 _17220 _17221 _17217) (@lem1042257 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042272 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042273 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term374 _17217 _17218 _17221 _17219 _17220) = (term375 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042272 (_17218 = _17219) (term296 _17220 _17221 _17217) (term352 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042295 (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term373 _17217 _17221 _17220 _17218 _17219) = (term375 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042268 _17217 _17218 _17221 _17219 _17220) (@lem1042273 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042296 (_17218 : nat) (_17219 : nat) (_17216 : nat) : (term356 _17218 _17219 _17216) = (term356 _17218 _17219 _17216).
Proof. exact (eq_refl (term356 _17218 _17219 _17216)). Qed.
Lemma lem1042297 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term376 _17216 _17217 _17221 _17220 _17218 _17219) = (term377 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042296 _17218 _17219 _17216) (@lem1042295 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042301 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042302 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term377 _17216 _17217 _17218 _17221 _17219 _17220) = (term378 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042301 (_17218 = _17219) (term296 _17218 _17219 _17216) (term367 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042336 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term376 _17216 _17217 _17221 _17220 _17218 _17219) = (term378 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042297 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042302 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042337 (_17220 : nat) (_17221 : nat) : (term62 _17220 _17221) = (term62 _17220 _17221).
Proof. exact (eq_refl (term62 _17220 _17221)). Qed.
Lemma lem1042338 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term379 _17216 _17217 _17221 _17220 _17218 _17219) = (term380 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042337 _17220 _17221) (@lem1042336 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042342 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042343 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term380 _17216 _17217 _17218 _17221 _17219 _17220) = (term368 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (@lem1042342 (_17218 = _17219) (_17220 = _17221) (term381 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042389 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term379 _17216 _17217 _17221 _17220 _17218 _17219) = (term368 _17216 _17217 _17218 _17221 _17219 _17220).
Proof. exact (TRANS (@lem1042338 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042343 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042390 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : ((term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term379 _17216 _17217 _17221 _17220 _17218 _17219)) = ((term368 _17216 _17217 _17218 _17221 _17219 _17220) = (term368 _17216 _17217 _17218 _17221 _17219 _17220)).
Proof. exact (MK_COMB (@lem1042216 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042389 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042392 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1042393 (x : Prop) : (x = x) = True.
Proof. exact (@lem1042392 Prop x). Qed.
Lemma lem1042394 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : ((term368 _17216 _17217 _17218 _17221 _17219 _17220) = (term368 _17216 _17217 _17218 _17221 _17219 _17220)) = True.
Proof. exact (@lem1042393 (term368 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042395 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : ((term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term379 _17216 _17217 _17221 _17220 _17218 _17219)) = True.
Proof. exact (TRANS (@lem1042390 _17216 _17217 _17218 _17221 _17219 _17220) (@lem1042394 _17216 _17217 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042396 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : True = ((term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term379 _17216 _17217 _17221 _17220 _17218 _17219)).
Proof. exact (SYM (@lem1042395 _17216 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042397 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term295 _17216 _17217 _17218 _17219 _17220 _17221) = (term379 _17216 _17217 _17221 _17220 _17218 _17219).
Proof. exact (EQ_MP (@lem1042396 _17216 _17217 _17221 _17220 _17218 _17219) (@lem0)). Qed.
Lemma lem1042398 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) (h1 : term107) : term379 _17216 _17217 _17221 _17220 _17218 _17219.
Proof. exact (EQ_MP (@lem1042397 _17216 _17217 _17221 _17220 _17218 _17219) (@lem1041668 _17216 _17217 _17218 _17219 _17220 _17221 h1)). Qed.
Lemma lem1042400 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1042401 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term379 _17216 _17217 _17221 _17220 _17218 _17219) = (term382 _17216 _17217 _17218 _17219 _17220 _17221).
Proof. exact (@lem1042400 (term376 _17216 _17217 _17221 _17220 _17218 _17219) (_17220 = _17221)). Qed.
Lemma lem1042403 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042404 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term383 _17216 _17217 _17221 _17220 _17218 _17219) = (term384 _17216 _17217 _17221 _17220 _17218 _17219).
Proof. exact (@lem1042403 (term296 _17218 _17219 _17216) (term373 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042406 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042407 (_17218 : nat) (_17219 : nat) (_17216 : nat) : (term385 _17218 _17219 _17216) = (_17218 = (Nat.add _17219 _17216)).
Proof. exact (@lem1042406 (_17218 = (Nat.add _17219 _17216))). Qed.
Lemma lem1042408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042409 (_17218 : nat) (_17219 : nat) (_17216 : nat) : (term386 _17218 _17219 _17216) = (term387 _17218 _17219 _17216).
Proof. exact (MK_COMB (@lem1042408) (@lem1042407 _17218 _17219 _17216)). Qed.
Lemma lem1042411 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042412 (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term388 _17217 _17221 _17220 _17218 _17219) = (term389 _17217 _17221 _17220 _17218 _17219).
Proof. exact (@lem1042411 (term296 _17220 _17221 _17217) (term371 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042414 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042415 (_17220 : nat) (_17221 : nat) (_17217 : nat) : (term385 _17220 _17221 _17217) = (_17220 = (Nat.add _17221 _17217)).
Proof. exact (@lem1042414 (_17220 = (Nat.add _17221 _17217))). Qed.
Lemma lem1042416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042417 (_17220 : nat) (_17221 : nat) (_17217 : nat) : (term386 _17220 _17221 _17217) = (term387 _17220 _17221 _17217).
Proof. exact (MK_COMB (@lem1042416) (@lem1042415 _17220 _17221 _17217)). Qed.
Lemma lem1042419 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042420 (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term390 _17221 _17220 _17218 _17219) = (term391 _17221 _17220 _17218 _17219).
Proof. exact (@lem1042419 (term352 _17218 _17221 _17219 _17220) (_17218 = _17219)). Qed.
Lemma lem1042422 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042423 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term392 _17218 _17221 _17219 _17220) = ((term53 _17218 _17220 _17219 _17221) = (term53 _17218 _17221 _17219 _17220)).
Proof. exact (@lem1042422 ((term53 _17218 _17220 _17219 _17221) = (term53 _17218 _17221 _17219 _17220))). Qed.
Lemma lem1042424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042425 (_17218 : nat) (_17221 : nat) (_17219 : nat) (_17220 : nat) : (term393 _17218 _17221 _17219 _17220) = (term394 _17218 _17221 _17219 _17220).
Proof. exact (MK_COMB (@lem1042424) (@lem1042423 _17218 _17221 _17219 _17220)). Qed.
Lemma lem1042426 (_17218 : nat) (_17219 : nat) : (term260 _17218 _17219) = (term260 _17218 _17219).
Proof. exact (eq_refl (term260 _17218 _17219)). Qed.
Lemma lem1042427 (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term391 _17221 _17220 _17218 _17219) = (term395 _17221 _17220 _17218 _17219).
Proof. exact (MK_COMB (@lem1042425 _17218 _17221 _17219 _17220) (@lem1042426 _17218 _17219)). Qed.
Lemma lem1042428 (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term390 _17221 _17220 _17218 _17219) = (term395 _17221 _17220 _17218 _17219).
Proof. exact (TRANS (@lem1042420 _17221 _17220 _17218 _17219) (@lem1042427 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042429 (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term389 _17217 _17221 _17220 _17218 _17219) = (term396 _17217 _17221 _17220 _17218 _17219).
Proof. exact (MK_COMB (@lem1042417 _17220 _17221 _17217) (@lem1042428 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042430 (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term388 _17217 _17221 _17220 _17218 _17219) = (term396 _17217 _17221 _17220 _17218 _17219).
Proof. exact (TRANS (@lem1042412 _17217 _17221 _17220 _17218 _17219) (@lem1042429 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042431 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term384 _17216 _17217 _17221 _17220 _17218 _17219) = (term397 _17216 _17217 _17221 _17220 _17218 _17219).
Proof. exact (MK_COMB (@lem1042409 _17218 _17219 _17216) (@lem1042430 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042432 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term383 _17216 _17217 _17221 _17220 _17218 _17219) = (term397 _17216 _17217 _17221 _17220 _17218 _17219).
Proof. exact (TRANS (@lem1042404 _17216 _17217 _17221 _17220 _17218 _17219) (@lem1042431 _17216 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1042434 (_17216 : nat) (_17217 : nat) (_17221 : nat) (_17220 : nat) (_17218 : nat) (_17219 : nat) : (term398 _17216 _17217 _17221 _17220 _17218 _17219) = (term399 _17216 _17217 _17221 _17220 _17218 _17219).
Proof. exact (MK_COMB (@lem1042433) (@lem1042432 _17216 _17217 _17221 _17220 _17218 _17219)). Qed.
Lemma lem1042435 (_17220 : nat) (_17221 : nat) : (_17220 = _17221) = (_17220 = _17221).
Proof. exact (eq_refl (_17220 = _17221)). Qed.
Lemma lem1042436 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term382 _17216 _17217 _17218 _17219 _17220 _17221) = (term400 _17216 _17217 _17218 _17219 _17220 _17221).
Proof. exact (MK_COMB (@lem1042434 _17216 _17217 _17221 _17220 _17218 _17219) (@lem1042435 _17220 _17221)). Qed.
Lemma lem1042437 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) : (term379 _17216 _17217 _17221 _17220 _17218 _17219) = (term400 _17216 _17217 _17218 _17219 _17220 _17221).
Proof. exact (TRANS (@lem1042401 _17216 _17217 _17218 _17219 _17220 _17221) (@lem1042436 _17216 _17217 _17218 _17219 _17220 _17221)). Qed.
Lemma lem1042439 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term401 y d d' x.
Proof. exact (conj (@lem1042007 d' x y d h1) (@lem1042014 d' x y d h1)). Qed.
Lemma lem1042440 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term402 y d d' x.
Proof. exact (conj (@lem1041868 y d) (@lem1042439 d' x y d h1)). Qed.
Lemma lem1042441 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term403 y d d' x.
Proof. exact (conj (@lem1041860 x d') (@lem1042440 d' x y d h1)). Qed.
Lemma lem1042443 (_17216 : nat) (_17217 : nat) (_17218 : nat) (_17219 : nat) (_17220 : nat) (_17221 : nat) (h1 : term107) : term400 _17216 _17217 _17218 _17219 _17220 _17221.
Proof. exact (EQ_MP (@lem1042437 _17216 _17217 _17218 _17219 _17220 _17221) (@lem1042398 _17216 _17217 _17221 _17220 _17218 _17219 h1)). Qed.
Lemma lem1042444 (d' : nat) (x : nat) (d : nat) (y : nat) (h1 : term107) : term404 d' x d y.
Proof. exact (@lem1042443 d' d (Nat.add x d') x (Nat.add y d) y h1). Qed.
Lemma lem1042447 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : (Nat.add y d) = y.
Proof. exact (@lem1042444 d' x d y h1 (@lem1042441 d' x y d h2)). Qed.
Lemma lem1042448 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : term405 d y.
Proof. exact (fun h0 : term349 d y => @lem1042447 d' x y d h1 h2). Qed.
Lemma lem1042450 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042451 (d : nat) (y : nat) : (term405 d y) = ((Nat.add y d) = y).
Proof. exact (@lem1042450 ((Nat.add y d) = y)). Qed.
Lemma lem1042452 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : (Nat.add y d) = y.
Proof. exact (EQ_MP (@lem1042451 d y) (@lem1042448 d' x y d h1 h2)). Qed.
Lemma lem1042454 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042455 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1042454 (Nat.add y d)). Qed.
Lemma lem1042456 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1042455 y d). Qed.
Lemma lem1042458 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042459 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1042458 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1042460 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1042459 y d) (@lem1042456 y d)). Qed.
Lemma lem1042461 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : term406 y d.
Proof. exact (conj (@lem1042452 d' x y d h1 h2) (@lem1042460 y d)). Qed.
Lemma lem1042463 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1041994 x y z) (@lem1041973 y x z)). Qed.
Lemma lem1042464 (y : nat) (d : nat) : term407 y d.
Proof. exact (@lem1042463 (Nat.add y d) y (Nat.add y d)). Qed.
Lemma lem1042467 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : y = (Nat.add y d).
Proof. exact (@lem1042464 y d (@lem1042461 d' x y d h1 h2)). Qed.
Lemma lem1042468 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : term408 y d.
Proof. exact (fun h0 : term294 y d => @lem1042467 d' x y d h1 h2). Qed.
Lemma lem1042470 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042471 (y : nat) (d : nat) : (term408 y d) = (y = (Nat.add y d)).
Proof. exact (@lem1042470 (y = (Nat.add y d))). Qed.
Lemma lem1042472 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : y = (Nat.add y d).
Proof. exact (EQ_MP (@lem1042471 y d) (@lem1042468 d' x y d h1 h2)). Qed.
Lemma lem1042475 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1042477 (y : nat) (d : nat) : (term294 y d) = (term409 y d).
Proof. exact (@lem1042475 (y = (Nat.add y d))). Qed.
Lemma lem1042480 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term608 d' x y d) : term409 y d.
Proof. exact (EQ_MP (@lem1042477 y d) (@lem1041648 d' x y d h1)). Qed.
Lemma lem1042483 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : False.
Proof. exact (@lem1042480 d' x y d h2 (@lem1042472 d' x y d h1 h2)). Qed.
Lemma lem1042484 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : term410.
Proof. exact (fun h0 : ~ False => @lem1042483 d' x y d h1 h2). Qed.
Lemma lem1042486 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042487 : term410 = False.
Proof. exact (@lem1042486 False). Qed.
Lemma lem1042488 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term608 d' x y d) : False.
Proof. exact (EQ_MP (@lem1042487) (@lem1042484 d' x y d h1 h2)). Qed.
Lemma lem1042520 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1042522 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042523 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1042522 (Nat.add x d')). Qed.
Lemma lem1042524 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1042523 x d'). Qed.
Lemma lem1042526 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042527 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1042526 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1042528 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1042527 x d') (@lem1042524 x d')). Qed.
Lemma lem1042530 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042531 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1042530 (Nat.add y d)). Qed.
Lemma lem1042532 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1042531 y d). Qed.
Lemma lem1042534 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042535 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1042534 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1042536 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1042535 y d) (@lem1042532 y d)). Qed.
Lemma lem1042538 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1042539 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term405 d' x.
Proof. exact (fun h0 : term349 d' x => @lem1042538 d' x h1). Qed.
Lemma lem1042541 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042542 (d' : nat) (x : nat) : (term405 d' x) = ((Nat.add x d') = x).
Proof. exact (@lem1042541 ((Nat.add x d') = x)). Qed.
Lemma lem1042543 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (EQ_MP (@lem1042542 d' x) (@lem1042539 d' x h1)). Qed.
Lemma lem1042561 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042562 (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term415 _17227 _17231 _17230 _17228 _17229) = (term416 _17230 _17231 _17227 _17228 _17229).
Proof. exact (@lem1042561 ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230)) (term296 _17230 _17231 _17227) (term260 _17228 _17229)). Qed.
Lemma lem1042578 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1042579 (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term417 _17230 _17231 _17227 _17228 _17229) = (term418 _17228 _17229 _17230 _17231 _17227).
Proof. exact (@lem1042578 (term260 _17228 _17229) (term296 _17230 _17231 _17227)). Qed.
Lemma lem1042589 (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term236 _17228 _17231 _17229 _17230) = (term236 _17228 _17231 _17229 _17230).
Proof. exact (eq_refl (term236 _17228 _17231 _17229 _17230)). Qed.
Lemma lem1042590 (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term416 _17230 _17231 _17227 _17228 _17229) = (term419 _17228 _17229 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042589 _17228 _17231 _17229 _17230) (@lem1042579 _17228 _17229 _17230 _17231 _17227)). Qed.
Lemma lem1042601 (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term415 _17227 _17231 _17230 _17228 _17229) = (term419 _17228 _17229 _17230 _17231 _17227).
Proof. exact (TRANS (@lem1042562 _17230 _17231 _17227 _17228 _17229) (@lem1042590 _17228 _17229 _17230 _17231 _17227)). Qed.
Lemma lem1042602 (_17228 : nat) (_17229 : nat) (_17226 : nat) : (term356 _17228 _17229 _17226) = (term356 _17228 _17229 _17226).
Proof. exact (eq_refl (term356 _17228 _17229 _17226)). Qed.
Lemma lem1042603 (_17226 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term420 _17226 _17228 _17229 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042602 _17228 _17229 _17226) (@lem1042601 _17228 _17229 _17230 _17231 _17227)). Qed.
Lemma lem1042607 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042608 (_17226 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term420 _17226 _17228 _17229 _17230 _17231 _17227) = (term421 _17226 _17228 _17229 _17230 _17231 _17227).
Proof. exact (@lem1042607 ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230)) (term296 _17228 _17229 _17226) (term418 _17228 _17229 _17230 _17231 _17227)). Qed.
Lemma lem1042624 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042625 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term422 _17226 _17228 _17229 _17230 _17231 _17227) = (term423 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (@lem1042624 (term260 _17228 _17229) (term296 _17228 _17229 _17226) (term296 _17230 _17231 _17227)). Qed.
Lemma lem1042647 (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term236 _17228 _17231 _17229 _17230) = (term236 _17228 _17231 _17229 _17230).
Proof. exact (eq_refl (term236 _17228 _17231 _17229 _17230)). Qed.
Lemma lem1042648 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term421 _17226 _17228 _17229 _17230 _17231 _17227) = (term424 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042647 _17228 _17231 _17229 _17230) (@lem1042625 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042659 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term420 _17226 _17228 _17229 _17230 _17231 _17227) = (term424 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (TRANS (@lem1042608 _17226 _17228 _17229 _17230 _17231 _17227) (@lem1042648 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042660 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term424 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (TRANS (@lem1042603 _17226 _17228 _17229 _17230 _17231 _17227) (@lem1042659 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1042662 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term425 _17226 _17227 _17231 _17230 _17228 _17229) = (term426 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042661) (@lem1042660 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042690 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1042691 (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term417 _17230 _17231 _17227 _17228 _17229) = (term418 _17228 _17229 _17230 _17231 _17227).
Proof. exact (@lem1042690 (term260 _17228 _17229) (term296 _17230 _17231 _17227)). Qed.
Lemma lem1042701 (_17228 : nat) (_17229 : nat) (_17226 : nat) : (term356 _17228 _17229 _17226) = (term356 _17228 _17229 _17226).
Proof. exact (eq_refl (term356 _17228 _17229 _17226)). Qed.
Lemma lem1042702 (_17226 : nat) (_17228 : nat) (_17229 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term427 _17226 _17230 _17231 _17227 _17228 _17229) = (term422 _17226 _17228 _17229 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042701 _17228 _17229 _17226) (@lem1042691 _17228 _17229 _17230 _17231 _17227)). Qed.
Lemma lem1042706 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042707 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term422 _17226 _17228 _17229 _17230 _17231 _17227) = (term423 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (@lem1042706 (term260 _17228 _17229) (term296 _17228 _17229 _17226) (term296 _17230 _17231 _17227)). Qed.
Lemma lem1042729 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term427 _17226 _17230 _17231 _17227 _17228 _17229) = (term423 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (TRANS (@lem1042702 _17226 _17228 _17229 _17230 _17231 _17227) (@lem1042707 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042730 (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term236 _17228 _17231 _17229 _17230) = (term236 _17228 _17231 _17229 _17230).
Proof. exact (eq_refl (term236 _17228 _17231 _17229 _17230)). Qed.
Lemma lem1042731 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term428 _17226 _17230 _17231 _17227 _17228 _17229) = (term424 _17228 _17229 _17226 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042730 _17228 _17231 _17229 _17230) (@lem1042729 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042742 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : ((term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term428 _17226 _17230 _17231 _17227 _17228 _17229)) = ((term424 _17228 _17229 _17226 _17230 _17231 _17227) = (term424 _17228 _17229 _17226 _17230 _17231 _17227)).
Proof. exact (MK_COMB (@lem1042662 _17228 _17229 _17226 _17230 _17231 _17227) (@lem1042731 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042744 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1042745 (x : Prop) : (x = x) = True.
Proof. exact (@lem1042744 Prop x). Qed.
Lemma lem1042746 (_17228 : nat) (_17229 : nat) (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) : ((term424 _17228 _17229 _17226 _17230 _17231 _17227) = (term424 _17228 _17229 _17226 _17230 _17231 _17227)) = True.
Proof. exact (@lem1042745 (term424 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042747 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : ((term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term428 _17226 _17230 _17231 _17227 _17228 _17229)) = True.
Proof. exact (TRANS (@lem1042742 _17228 _17229 _17226 _17230 _17231 _17227) (@lem1042746 _17228 _17229 _17226 _17230 _17231 _17227)). Qed.
Lemma lem1042748 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : True = ((term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term428 _17226 _17230 _17231 _17227 _17228 _17229)).
Proof. exact (SYM (@lem1042747 _17226 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042749 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term298 _17226 _17227 _17231 _17230 _17228 _17229) = (term428 _17226 _17230 _17231 _17227 _17228 _17229).
Proof. exact (EQ_MP (@lem1042748 _17226 _17230 _17231 _17227 _17228 _17229) (@lem0)). Qed.
Lemma lem1042750 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) (h1 : term107) : term428 _17226 _17230 _17231 _17227 _17228 _17229.
Proof. exact (EQ_MP (@lem1042749 _17226 _17230 _17231 _17227 _17228 _17229) (@lem1041744 _17226 _17227 _17231 _17230 _17228 _17229 h1)). Qed.
Lemma lem1042752 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1042753 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term428 _17226 _17230 _17231 _17227 _17228 _17229) = (term429 _17226 _17227 _17228 _17231 _17229 _17230).
Proof. exact (@lem1042752 (term427 _17226 _17230 _17231 _17227 _17228 _17229) ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230))). Qed.
Lemma lem1042755 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042756 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term430 _17226 _17230 _17231 _17227 _17228 _17229) = (term431 _17226 _17230 _17231 _17227 _17228 _17229).
Proof. exact (@lem1042755 (term296 _17228 _17229 _17226) (term417 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042758 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042759 (_17228 : nat) (_17229 : nat) (_17226 : nat) : (term385 _17228 _17229 _17226) = (_17228 = (Nat.add _17229 _17226)).
Proof. exact (@lem1042758 (_17228 = (Nat.add _17229 _17226))). Qed.
Lemma lem1042760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042761 (_17228 : nat) (_17229 : nat) (_17226 : nat) : (term386 _17228 _17229 _17226) = (term387 _17228 _17229 _17226).
Proof. exact (MK_COMB (@lem1042760) (@lem1042759 _17228 _17229 _17226)). Qed.
Lemma lem1042763 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042764 (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term432 _17230 _17231 _17227 _17228 _17229) = (term433 _17230 _17231 _17227 _17228 _17229).
Proof. exact (@lem1042763 (term296 _17230 _17231 _17227) (term260 _17228 _17229)). Qed.
Lemma lem1042766 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042767 (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term385 _17230 _17231 _17227) = (_17230 = (Nat.add _17231 _17227)).
Proof. exact (@lem1042766 (_17230 = (Nat.add _17231 _17227))). Qed.
Lemma lem1042768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042769 (_17230 : nat) (_17231 : nat) (_17227 : nat) : (term386 _17230 _17231 _17227) = (term387 _17230 _17231 _17227).
Proof. exact (MK_COMB (@lem1042768) (@lem1042767 _17230 _17231 _17227)). Qed.
Lemma lem1042771 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042772 (_17228 : nat) (_17229 : nat) : (term321 _17228 _17229) = (_17228 = _17229).
Proof. exact (@lem1042771 (_17228 = _17229)). Qed.
Lemma lem1042773 (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term433 _17230 _17231 _17227 _17228 _17229) = (term434 _17230 _17231 _17227 _17228 _17229).
Proof. exact (MK_COMB (@lem1042769 _17230 _17231 _17227) (@lem1042772 _17228 _17229)). Qed.
Lemma lem1042774 (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term432 _17230 _17231 _17227 _17228 _17229) = (term434 _17230 _17231 _17227 _17228 _17229).
Proof. exact (TRANS (@lem1042764 _17230 _17231 _17227 _17228 _17229) (@lem1042773 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042775 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term431 _17226 _17230 _17231 _17227 _17228 _17229) = (term435 _17226 _17230 _17231 _17227 _17228 _17229).
Proof. exact (MK_COMB (@lem1042761 _17228 _17229 _17226) (@lem1042774 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042776 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term430 _17226 _17230 _17231 _17227 _17228 _17229) = (term435 _17226 _17230 _17231 _17227 _17228 _17229).
Proof. exact (TRANS (@lem1042756 _17226 _17230 _17231 _17227 _17228 _17229) (@lem1042775 _17226 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1042778 (_17226 : nat) (_17230 : nat) (_17231 : nat) (_17227 : nat) (_17228 : nat) (_17229 : nat) : (term436 _17226 _17230 _17231 _17227 _17228 _17229) = (term437 _17226 _17230 _17231 _17227 _17228 _17229).
Proof. exact (MK_COMB (@lem1042777) (@lem1042776 _17226 _17230 _17231 _17227 _17228 _17229)). Qed.
Lemma lem1042779 (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230)) = ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230)).
Proof. exact (eq_refl ((term53 _17228 _17230 _17229 _17231) = (term53 _17228 _17231 _17229 _17230))). Qed.
Lemma lem1042780 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term429 _17226 _17227 _17228 _17231 _17229 _17230) = (term438 _17226 _17227 _17228 _17231 _17229 _17230).
Proof. exact (MK_COMB (@lem1042778 _17226 _17230 _17231 _17227 _17228 _17229) (@lem1042779 _17228 _17231 _17229 _17230)). Qed.
Lemma lem1042781 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) : (term428 _17226 _17230 _17231 _17227 _17228 _17229) = (term438 _17226 _17227 _17228 _17231 _17229 _17230).
Proof. exact (TRANS (@lem1042753 _17226 _17227 _17228 _17231 _17229 _17230) (@lem1042780 _17226 _17227 _17228 _17231 _17229 _17230)). Qed.
Lemma lem1042783 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term439 y d d' x.
Proof. exact (conj (@lem1042536 y d) (@lem1042543 d' x h1)). Qed.
Lemma lem1042784 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term440 y d d' x.
Proof. exact (conj (@lem1042528 x d') (@lem1042783 y d d' x h1)). Qed.
Lemma lem1042786 (_17226 : nat) (_17227 : nat) (_17228 : nat) (_17231 : nat) (_17229 : nat) (_17230 : nat) (h1 : term107) : term438 _17226 _17227 _17228 _17231 _17229 _17230.
Proof. exact (EQ_MP (@lem1042781 _17226 _17227 _17228 _17231 _17229 _17230) (@lem1042750 _17226 _17230 _17231 _17227 _17228 _17229 h1)). Qed.
Lemma lem1042787 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) : term441 d' x y d.
Proof. exact (@lem1042786 d' d (Nat.add x d') y x (Nat.add y d) h1). Qed.
Lemma lem1042790 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (@lem1042787 d' x y d h1 (@lem1042784 y d d' x h2)). Qed.
Lemma lem1042791 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : term336 d' x y d.
Proof. exact (fun h0 : term337 d' x y d => @lem1042790 y d d' x h1 h2). Qed.
Lemma lem1042793 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042794 (d' : nat) (x : nat) (y : nat) (d : nat) : (term336 d' x y d) = ((term54 d' d x y) = (term58 d' x y d)).
Proof. exact (@lem1042793 ((term54 d' d x y) = (term58 d' x y d))). Qed.
Lemma lem1042795 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (EQ_MP (@lem1042794 d' x y d) (@lem1042791 y d d' x h1 h2)). Qed.
Lemma lem1042797 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042798 (d' : nat) (d : nat) (x : nat) (y : nat) : (term54 d' d x y) = (term54 d' d x y).
Proof. exact (@lem1042797 (term54 d' d x y)). Qed.
Lemma lem1042799 (d' : nat) (d : nat) (x : nat) (y : nat) : term619 d' d x y.
Proof. exact (fun h0 : term620 d' d x y => @lem1042798 d' d x y). Qed.
Lemma lem1042801 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042802 (d' : nat) (d : nat) (x : nat) (y : nat) : (term619 d' d x y) = ((term54 d' d x y) = (term54 d' d x y)).
Proof. exact (@lem1042801 ((term54 d' d x y) = (term54 d' d x y))). Qed.
Lemma lem1042803 (d' : nat) (d : nat) (x : nat) (y : nat) : (term54 d' d x y) = (term54 d' d x y).
Proof. exact (EQ_MP (@lem1042802 d' d x y) (@lem1042799 d' d x y)). Qed.
Lemma lem1042821 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1042822 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1042821 (y = z) (term260 x z)). Qed.
Lemma lem1042832 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1042833 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1042832 x y) (@lem1042822 y x z)). Qed.
Lemma lem1042837 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1042838 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1042837 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1042860 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1042833 y x z) (@lem1042838 y x z)). Qed.
Lemma lem1042861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1042862 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1042861) (@lem1042860 y x z)). Qed.
Lemma lem1042884 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1042885 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1042862 y x z) (@lem1042884 y x z)). Qed.
Lemma lem1042887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1042888 (x : Prop) : (x = x) = True.
Proof. exact (@lem1042887 Prop x). Qed.
Lemma lem1042889 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1042888 (term310 y x z)). Qed.
Lemma lem1042890 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1042885 y x z) (@lem1042889 y x z)). Qed.
Lemma lem1042891 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1042890 y x z)). Qed.
Lemma lem1042892 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1042891 y x z) (@lem0)). Qed.
Lemma lem1042893 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1042892 y x z) (@lem1042520 x y z)). Qed.
Lemma lem1042895 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1042896 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1042895 (term315 y x z) (y = z)). Qed.
Lemma lem1042898 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1042899 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1042898 (term260 x y) (term260 x z)). Qed.
Lemma lem1042901 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042902 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1042901 (x = y)). Qed.
Lemma lem1042903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1042904 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1042903) (@lem1042902 x y)). Qed.
Lemma lem1042906 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1042907 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1042906 (x = z)). Qed.
Lemma lem1042908 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1042904 x y) (@lem1042907 x z)). Qed.
Lemma lem1042909 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1042899 y x z) (@lem1042908 y x z)). Qed.
Lemma lem1042910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1042911 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1042910) (@lem1042909 y x z)). Qed.
Lemma lem1042912 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1042913 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1042911 y x z) (@lem1042912 y z)). Qed.
Lemma lem1042914 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1042896 x y z) (@lem1042913 x y z)). Qed.
Lemma lem1042916 (d : nat) (y : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : term621 d' d x y.
Proof. exact (conj (@lem1042795 y d d' x h1 h2) (@lem1042803 d' d x y)). Qed.
Lemma lem1042918 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1042914 x y z) (@lem1042893 y x z)). Qed.
Lemma lem1042919 (d' : nat) (d : nat) (x : nat) (y : nat) : term622 d' d x y.
Proof. exact (@lem1042918 (term54 d' d x y) (term58 d' x y d) (term54 d' d x y)). Qed.
Lemma lem1042922 (d : nat) (y : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (@lem1042919 d' d x y (@lem1042916 d y d' x h1 h2)). Qed.
Lemma lem1042923 (d : nat) (y : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : term614 d' d x y.
Proof. exact (fun h0 : term613 d' d x y => @lem1042922 d y d' x h1 h2). Qed.
Lemma lem1042925 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042926 (d' : nat) (d : nat) (x : nat) (y : nat) : (term614 d' d x y) = ((term58 d' x y d) = (term54 d' d x y)).
Proof. exact (@lem1042925 ((term58 d' x y d) = (term54 d' d x y))). Qed.
Lemma lem1042927 (d : nat) (y : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (EQ_MP (@lem1042926 d' d x y) (@lem1042923 d y d' x h1 h2)). Qed.
Lemma lem1042930 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1042932 (d' : nat) (d : nat) (x : nat) (y : nat) : (term613 d' d x y) = (term623 d' d x y).
Proof. exact (@lem1042930 ((term58 d' x y d) = (term54 d' d x y))). Qed.
Lemma lem1042935 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term623 d' d x y.
Proof. exact (EQ_MP (@lem1042932 d' d x y) (@lem1041706 d' x y d h1)). Qed.
Lemma lem1042938 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : False.
Proof. exact (@lem1042935 d' x y d h2 (@lem1042927 d y d' x h1 h3)). Qed.
Lemma lem1042939 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : term410.
Proof. exact (fun h0 : ~ False => @lem1042938 y d d' x h1 h2 h3). Qed.
Lemma lem1042941 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042942 : term410 = False.
Proof. exact (@lem1042941 False). Qed.
Lemma lem1042943 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1042942) (@lem1042939 y d d' x h1 h2 h3)). Qed.
Lemma lem1042975 (x : nat) (y : nat) (z : nat) : term299 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1042977 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042978 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1042977 (Nat.add x d')). Qed.
Lemma lem1042979 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1042978 x d'). Qed.
Lemma lem1042981 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042982 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1042981 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1042983 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1042982 x d') (@lem1042979 x d')). Qed.
Lemma lem1042985 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1042986 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (@lem1042985 (Nat.add y d)). Qed.
Lemma lem1042987 (y : nat) (d : nat) : term300 y d.
Proof. exact (fun h0 : term301 y d => @lem1042986 y d). Qed.
Lemma lem1042989 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042990 (y : nat) (d : nat) : (term300 y d) = ((Nat.add y d) = (Nat.add y d)).
Proof. exact (@lem1042989 ((Nat.add y d) = (Nat.add y d))). Qed.
Lemma lem1042991 (y : nat) (d : nat) : (Nat.add y d) = (Nat.add y d).
Proof. exact (EQ_MP (@lem1042990 y d) (@lem1042987 y d)). Qed.
Lemma lem1042993 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (h1). Qed.
Lemma lem1042994 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term408 y d.
Proof. exact (fun h0 : term294 y d => @lem1042993 y d h1). Qed.
Lemma lem1042996 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1042997 (y : nat) (d : nat) : (term408 y d) = (y = (Nat.add y d)).
Proof. exact (@lem1042996 (y = (Nat.add y d))). Qed.
Lemma lem1042998 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : y = (Nat.add y d).
Proof. exact (EQ_MP (@lem1042997 y d) (@lem1042994 y d h1)). Qed.
Lemma lem1043000 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1043001 (y : nat) : y = y.
Proof. exact (@lem1043000 y). Qed.
Lemma lem1043002 (y : nat) : term411 y.
Proof. exact (fun h0 : term412 y => @lem1043001 y). Qed.
Lemma lem1043004 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043005 (y : nat) : (term411 y) = (y = y).
Proof. exact (@lem1043004 (y = y)). Qed.
Lemma lem1043006 (y : nat) : y = y.
Proof. exact (EQ_MP (@lem1043005 y) (@lem1043002 y)). Qed.
Lemma lem1043024 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1043025 (y : nat) (x : nat) (z : nat) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1043024 (y = z) (term260 x z)). Qed.
Lemma lem1043035 (x : nat) (y : nat) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1043036 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1043035 x y) (@lem1043025 y x z)). Qed.
Lemma lem1043040 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1043041 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term310 y x z).
Proof. exact (@lem1043040 (y = z) (term260 x y) (term260 x z)). Qed.
Lemma lem1043063 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (TRANS (@lem1043036 y x z) (@lem1043041 y x z)). Qed.
Lemma lem1043064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1043065 (y : nat) (x : nat) (z : nat) : (term311 x y z) = (term312 y x z).
Proof. exact (MK_COMB (@lem1043064) (@lem1043063 y x z)). Qed.
Lemma lem1043087 (y : nat) (x : nat) (z : nat) : (term310 y x z) = (term310 y x z).
Proof. exact (eq_refl (term310 y x z)). Qed.
Lemma lem1043088 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = ((term310 y x z) = (term310 y x z)).
Proof. exact (MK_COMB (@lem1043065 y x z) (@lem1043087 y x z)). Qed.
Lemma lem1043090 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1043091 (x : Prop) : (x = x) = True.
Proof. exact (@lem1043090 Prop x). Qed.
Lemma lem1043092 (y : nat) (x : nat) (z : nat) : ((term310 y x z) = (term310 y x z)) = True.
Proof. exact (@lem1043091 (term310 y x z)). Qed.
Lemma lem1043093 (y : nat) (x : nat) (z : nat) : ((term299 x y z) = (term310 y x z)) = True.
Proof. exact (TRANS (@lem1043088 y x z) (@lem1043092 y x z)). Qed.
Lemma lem1043094 (y : nat) (x : nat) (z : nat) : True = ((term299 x y z) = (term310 y x z)).
Proof. exact (SYM (@lem1043093 y x z)). Qed.
Lemma lem1043095 (y : nat) (x : nat) (z : nat) : (term299 x y z) = (term310 y x z).
Proof. exact (EQ_MP (@lem1043094 y x z) (@lem0)). Qed.
Lemma lem1043096 (y : nat) (x : nat) (z : nat) : term310 y x z.
Proof. exact (EQ_MP (@lem1043095 y x z) (@lem1042975 x y z)). Qed.
Lemma lem1043098 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1043099 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term314 x y z).
Proof. exact (@lem1043098 (term315 y x z) (y = z)). Qed.
Lemma lem1043101 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1043102 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term319 y x z).
Proof. exact (@lem1043101 (term260 x y) (term260 x z)). Qed.
Lemma lem1043104 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1043105 (x : nat) (y : nat) : (term321 x y) = (x = y).
Proof. exact (@lem1043104 (x = y)). Qed.
Lemma lem1043106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1043107 (x : nat) (y : nat) : (term322 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1043106) (@lem1043105 x y)). Qed.
Lemma lem1043109 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1043110 (x : nat) (z : nat) : (term321 x z) = (x = z).
Proof. exact (@lem1043109 (x = z)). Qed.
Lemma lem1043111 (y : nat) (x : nat) (z : nat) : (term319 y x z) = (term324 y x z).
Proof. exact (MK_COMB (@lem1043107 x y) (@lem1043110 x z)). Qed.
Lemma lem1043112 (y : nat) (x : nat) (z : nat) : (term318 y x z) = (term324 y x z).
Proof. exact (TRANS (@lem1043102 y x z) (@lem1043111 y x z)). Qed.
Lemma lem1043113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1043114 (y : nat) (x : nat) (z : nat) : (term325 y x z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1043113) (@lem1043112 y x z)). Qed.
Lemma lem1043115 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1043116 (x : nat) (y : nat) (z : nat) : (term314 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1043114 y x z) (@lem1043115 y z)). Qed.
Lemma lem1043117 (x : nat) (y : nat) (z : nat) : (term310 y x z) = (term327 x y z).
Proof. exact (TRANS (@lem1043099 x y z) (@lem1043116 x y z)). Qed.
Lemma lem1043119 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term413 d y.
Proof. exact (conj (@lem1042998 y d h1) (@lem1043006 y)). Qed.
Lemma lem1043121 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1043117 x y z) (@lem1043096 y x z)). Qed.
Lemma lem1043122 (d : nat) (y : nat) : term414 d y.
Proof. exact (@lem1043121 y (Nat.add y d) y). Qed.
Lemma lem1043125 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (Nat.add y d) = y.
Proof. exact (@lem1043122 d y (@lem1043119 y d h1)). Qed.
Lemma lem1043126 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term405 d y.
Proof. exact (fun h0 : term349 d y => @lem1043125 y d h1). Qed.
Lemma lem1043128 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043129 (d : nat) (y : nat) : (term405 d y) = ((Nat.add y d) = y).
Proof. exact (@lem1043128 ((Nat.add y d) = y)). Qed.
Lemma lem1043130 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : (Nat.add y d) = y.
Proof. exact (EQ_MP (@lem1043129 d y) (@lem1043126 y d h1)). Qed.
Lemma lem1043148 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1043149 (_17238 : nat) (_17239 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term550 _17237 _17238 _17239 _17240 _17241) = (term551 _17238 _17239 _17237 _17240 _17241).
Proof. exact (@lem1043148 ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240)) (term296 _17240 _17241 _17237) (term260 _17240 _17241)). Qed.
Lemma lem1043165 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1043166 (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term552 _17237 _17240 _17241) = (term553 _17240 _17241 _17237).
Proof. exact (@lem1043165 (term260 _17240 _17241) (term296 _17240 _17241 _17237)). Qed.
Lemma lem1043176 (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : (term236 _17238 _17241 _17239 _17240) = (term236 _17238 _17241 _17239 _17240).
Proof. exact (eq_refl (term236 _17238 _17241 _17239 _17240)). Qed.
Lemma lem1043177 (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term551 _17238 _17239 _17237 _17240 _17241) = (term554 _17238 _17239 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043176 _17238 _17241 _17239 _17240) (@lem1043166 _17240 _17241 _17237)). Qed.
Lemma lem1043188 (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term550 _17237 _17238 _17239 _17240 _17241) = (term554 _17238 _17239 _17240 _17241 _17237).
Proof. exact (TRANS (@lem1043149 _17238 _17239 _17237 _17240 _17241) (@lem1043177 _17238 _17239 _17240 _17241 _17237)). Qed.
Lemma lem1043189 (_17238 : nat) (_17239 : nat) (_17236 : nat) : (term356 _17238 _17239 _17236) = (term356 _17238 _17239 _17236).
Proof. exact (eq_refl (term356 _17238 _17239 _17236)). Qed.
Lemma lem1043190 (_17236 : nat) (_17238 : nat) (_17239 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term555 _17236 _17238 _17239 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043189 _17238 _17239 _17236) (@lem1043188 _17238 _17239 _17240 _17241 _17237)). Qed.
Lemma lem1043194 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1043195 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term555 _17236 _17238 _17239 _17240 _17241 _17237) = (term556 _17238 _17239 _17236 _17240 _17241 _17237).
Proof. exact (@lem1043194 ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240)) (term296 _17238 _17239 _17236) (term553 _17240 _17241 _17237)). Qed.
Lemma lem1043229 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term556 _17238 _17239 _17236 _17240 _17241 _17237).
Proof. exact (TRANS (@lem1043190 _17236 _17238 _17239 _17240 _17241 _17237) (@lem1043195 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1043231 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term557 _17236 _17237 _17238 _17239 _17240 _17241) = (term558 _17238 _17239 _17236 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043230) (@lem1043229 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043259 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1043260 (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term552 _17237 _17240 _17241) = (term553 _17240 _17241 _17237).
Proof. exact (@lem1043259 (term260 _17240 _17241) (term296 _17240 _17241 _17237)). Qed.
Lemma lem1043270 (_17238 : nat) (_17239 : nat) (_17236 : nat) : (term356 _17238 _17239 _17236) = (term356 _17238 _17239 _17236).
Proof. exact (eq_refl (term356 _17238 _17239 _17236)). Qed.
Lemma lem1043271 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term559 _17238 _17239 _17236 _17237 _17240 _17241) = (term560 _17238 _17239 _17236 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043270 _17238 _17239 _17236) (@lem1043260 _17240 _17241 _17237)). Qed.
Lemma lem1043282 (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : (term236 _17238 _17241 _17239 _17240) = (term236 _17238 _17241 _17239 _17240).
Proof. exact (eq_refl (term236 _17238 _17241 _17239 _17240)). Qed.
Lemma lem1043283 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term561 _17238 _17239 _17236 _17237 _17240 _17241) = (term556 _17238 _17239 _17236 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043282 _17238 _17241 _17239 _17240) (@lem1043271 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043294 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : ((term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term561 _17238 _17239 _17236 _17237 _17240 _17241)) = ((term556 _17238 _17239 _17236 _17240 _17241 _17237) = (term556 _17238 _17239 _17236 _17240 _17241 _17237)).
Proof. exact (MK_COMB (@lem1043231 _17238 _17239 _17236 _17240 _17241 _17237) (@lem1043283 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1043297 (x : Prop) : (x = x) = True.
Proof. exact (@lem1043296 Prop x). Qed.
Lemma lem1043298 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17240 : nat) (_17241 : nat) (_17237 : nat) : ((term556 _17238 _17239 _17236 _17240 _17241 _17237) = (term556 _17238 _17239 _17236 _17240 _17241 _17237)) = True.
Proof. exact (@lem1043297 (term556 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043299 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : ((term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term561 _17238 _17239 _17236 _17237 _17240 _17241)) = True.
Proof. exact (TRANS (@lem1043294 _17238 _17239 _17236 _17240 _17241 _17237) (@lem1043298 _17238 _17239 _17236 _17240 _17241 _17237)). Qed.
Lemma lem1043300 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : True = ((term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term561 _17238 _17239 _17236 _17237 _17240 _17241)).
Proof. exact (SYM (@lem1043299 _17238 _17239 _17236 _17237 _17240 _17241)). Qed.
Lemma lem1043301 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term538 _17236 _17237 _17238 _17239 _17240 _17241) = (term561 _17238 _17239 _17236 _17237 _17240 _17241).
Proof. exact (EQ_MP (@lem1043300 _17238 _17239 _17236 _17237 _17240 _17241) (@lem0)). Qed.
Lemma lem1043302 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) (h1 : term107) : term561 _17238 _17239 _17236 _17237 _17240 _17241.
Proof. exact (EQ_MP (@lem1043301 _17238 _17239 _17236 _17237 _17240 _17241) (@lem1041820 _17236 _17237 _17238 _17239 _17240 _17241 h1)). Qed.
Lemma lem1043304 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1043305 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : (term561 _17238 _17239 _17236 _17237 _17240 _17241) = (term562 _17236 _17237 _17238 _17241 _17239 _17240).
Proof. exact (@lem1043304 (term559 _17238 _17239 _17236 _17237 _17240 _17241) ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240))). Qed.
Lemma lem1043307 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1043308 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term563 _17238 _17239 _17236 _17237 _17240 _17241) = (term564 _17238 _17239 _17236 _17237 _17240 _17241).
Proof. exact (@lem1043307 (term296 _17238 _17239 _17236) (term552 _17237 _17240 _17241)). Qed.
Lemma lem1043310 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1043311 (_17238 : nat) (_17239 : nat) (_17236 : nat) : (term385 _17238 _17239 _17236) = (_17238 = (Nat.add _17239 _17236)).
Proof. exact (@lem1043310 (_17238 = (Nat.add _17239 _17236))). Qed.
Lemma lem1043312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1043313 (_17238 : nat) (_17239 : nat) (_17236 : nat) : (term386 _17238 _17239 _17236) = (term387 _17238 _17239 _17236).
Proof. exact (MK_COMB (@lem1043312) (@lem1043311 _17238 _17239 _17236)). Qed.
Lemma lem1043315 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1043316 (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term565 _17237 _17240 _17241) = (term566 _17237 _17240 _17241).
Proof. exact (@lem1043315 (term296 _17240 _17241 _17237) (term260 _17240 _17241)). Qed.
Lemma lem1043318 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1043319 (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term385 _17240 _17241 _17237) = (_17240 = (Nat.add _17241 _17237)).
Proof. exact (@lem1043318 (_17240 = (Nat.add _17241 _17237))). Qed.
Lemma lem1043320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1043321 (_17240 : nat) (_17241 : nat) (_17237 : nat) : (term386 _17240 _17241 _17237) = (term387 _17240 _17241 _17237).
Proof. exact (MK_COMB (@lem1043320) (@lem1043319 _17240 _17241 _17237)). Qed.
Lemma lem1043323 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1043324 (_17240 : nat) (_17241 : nat) : (term321 _17240 _17241) = (_17240 = _17241).
Proof. exact (@lem1043323 (_17240 = _17241)). Qed.
Lemma lem1043325 (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term566 _17237 _17240 _17241) = (term567 _17237 _17240 _17241).
Proof. exact (MK_COMB (@lem1043321 _17240 _17241 _17237) (@lem1043324 _17240 _17241)). Qed.
Lemma lem1043326 (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term565 _17237 _17240 _17241) = (term567 _17237 _17240 _17241).
Proof. exact (TRANS (@lem1043316 _17237 _17240 _17241) (@lem1043325 _17237 _17240 _17241)). Qed.
Lemma lem1043327 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term564 _17238 _17239 _17236 _17237 _17240 _17241) = (term568 _17238 _17239 _17236 _17237 _17240 _17241).
Proof. exact (MK_COMB (@lem1043313 _17238 _17239 _17236) (@lem1043326 _17237 _17240 _17241)). Qed.
Lemma lem1043328 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term563 _17238 _17239 _17236 _17237 _17240 _17241) = (term568 _17238 _17239 _17236 _17237 _17240 _17241).
Proof. exact (TRANS (@lem1043308 _17238 _17239 _17236 _17237 _17240 _17241) (@lem1043327 _17238 _17239 _17236 _17237 _17240 _17241)). Qed.
Lemma lem1043329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1043330 (_17238 : nat) (_17239 : nat) (_17236 : nat) (_17237 : nat) (_17240 : nat) (_17241 : nat) : (term569 _17238 _17239 _17236 _17237 _17240 _17241) = (term570 _17238 _17239 _17236 _17237 _17240 _17241).
Proof. exact (MK_COMB (@lem1043329) (@lem1043328 _17238 _17239 _17236 _17237 _17240 _17241)). Qed.
Lemma lem1043331 (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240)) = ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240)).
Proof. exact (eq_refl ((term53 _17238 _17240 _17239 _17241) = (term53 _17238 _17241 _17239 _17240))). Qed.
Lemma lem1043332 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : (term562 _17236 _17237 _17238 _17241 _17239 _17240) = (term571 _17236 _17237 _17238 _17241 _17239 _17240).
Proof. exact (MK_COMB (@lem1043330 _17238 _17239 _17236 _17237 _17240 _17241) (@lem1043331 _17238 _17241 _17239 _17240)). Qed.
Lemma lem1043333 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) : (term561 _17238 _17239 _17236 _17237 _17240 _17241) = (term571 _17236 _17237 _17238 _17241 _17239 _17240).
Proof. exact (TRANS (@lem1043305 _17236 _17237 _17238 _17241 _17239 _17240) (@lem1043332 _17236 _17237 _17238 _17241 _17239 _17240)). Qed.
Lemma lem1043335 (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term572 d y.
Proof. exact (conj (@lem1042991 y d) (@lem1043130 y d h1)). Qed.
Lemma lem1043336 (x : nat) (d' : nat) (y : nat) (d : nat) (h1 : y = (Nat.add y d)) : term573 x d' d y.
Proof. exact (conj (@lem1042983 x d') (@lem1043335 y d h1)). Qed.
Lemma lem1043338 (_17236 : nat) (_17237 : nat) (_17238 : nat) (_17241 : nat) (_17239 : nat) (_17240 : nat) (h1 : term107) : term571 _17236 _17237 _17238 _17241 _17239 _17240.
Proof. exact (EQ_MP (@lem1043333 _17236 _17237 _17238 _17241 _17239 _17240) (@lem1043302 _17238 _17239 _17236 _17237 _17240 _17241 h1)). Qed.
Lemma lem1043339 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) : term574 d' x y d.
Proof. exact (@lem1043338 d' d (Nat.add x d') y x (Nat.add y d) h1). Qed.
Lemma lem1043342 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (@lem1043339 d' x y d h1 (@lem1043336 x d' y d h2)). Qed.
Lemma lem1043343 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : term336 d' x y d.
Proof. exact (fun h0 : term337 d' x y d => @lem1043342 d' x y d h1 h2). Qed.
Lemma lem1043345 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043346 (d' : nat) (x : nat) (y : nat) (d : nat) : (term336 d' x y d) = ((term54 d' d x y) = (term58 d' x y d)).
Proof. exact (@lem1043345 ((term54 d' d x y) = (term58 d' x y d))). Qed.
Lemma lem1043347 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : (term54 d' d x y) = (term58 d' x y d).
Proof. exact (EQ_MP (@lem1043346 d' x y d) (@lem1043343 d' x y d h1 h2)). Qed.
Lemma lem1043349 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1043350 (d' : nat) (d : nat) (x : nat) (y : nat) : (term54 d' d x y) = (term54 d' d x y).
Proof. exact (@lem1043349 (term54 d' d x y)). Qed.
Lemma lem1043351 (d' : nat) (d : nat) (x : nat) (y : nat) : term619 d' d x y.
Proof. exact (fun h0 : term620 d' d x y => @lem1043350 d' d x y). Qed.
Lemma lem1043353 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043354 (d' : nat) (d : nat) (x : nat) (y : nat) : (term619 d' d x y) = ((term54 d' d x y) = (term54 d' d x y)).
Proof. exact (@lem1043353 ((term54 d' d x y) = (term54 d' d x y))). Qed.
Lemma lem1043355 (d' : nat) (d : nat) (x : nat) (y : nat) : (term54 d' d x y) = (term54 d' d x y).
Proof. exact (EQ_MP (@lem1043354 d' d x y) (@lem1043351 d' d x y)). Qed.
Lemma lem1043356 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : term621 d' d x y.
Proof. exact (conj (@lem1043347 d' x y d h1 h2) (@lem1043355 d' d x y)). Qed.
Lemma lem1043358 (x : nat) (y : nat) (z : nat) : term327 x y z.
Proof. exact (EQ_MP (@lem1043117 x y z) (@lem1043096 y x z)). Qed.
Lemma lem1043359 (d' : nat) (d : nat) (x : nat) (y : nat) : term622 d' d x y.
Proof. exact (@lem1043358 (term54 d' d x y) (term58 d' x y d) (term54 d' d x y)). Qed.
Lemma lem1043362 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (@lem1043359 d' d x y (@lem1043356 d' x y d h1 h2)). Qed.
Lemma lem1043363 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : term614 d' d x y.
Proof. exact (fun h0 : term613 d' d x y => @lem1043362 d' x y d h1 h2). Qed.
Lemma lem1043365 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043366 (d' : nat) (d : nat) (x : nat) (y : nat) : (term614 d' d x y) = ((term58 d' x y d) = (term54 d' d x y)).
Proof. exact (@lem1043365 ((term58 d' x y d) = (term54 d' d x y))). Qed.
Lemma lem1043367 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : y = (Nat.add y d)) : (term58 d' x y d) = (term54 d' d x y).
Proof. exact (EQ_MP (@lem1043366 d' d x y) (@lem1043363 d' x y d h1 h2)). Qed.
Lemma lem1043370 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1043372 (d' : nat) (d : nat) (x : nat) (y : nat) : (term613 d' d x y) = (term623 d' d x y).
Proof. exact (@lem1043370 ((term58 d' x y d) = (term54 d' d x y))). Qed.
Lemma lem1043375 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term605 d' x y d) : term623 d' d x y.
Proof. exact (EQ_MP (@lem1043372 d' d x y) (@lem1041766 d' x y d h1)). Qed.
Lemma lem1043378 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : False.
Proof. exact (@lem1043375 d' x y d h2 (@lem1043367 d' x y d h1 h3)). Qed.
Lemma lem1043379 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : term410.
Proof. exact (fun h0 : ~ False => @lem1043378 d' x y d h1 h2 h3). Qed.
Lemma lem1043381 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1043382 : term410 = False.
Proof. exact (@lem1043381 False). Qed.
Lemma lem1043383 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1043382) (@lem1043379 d' x y d h1 h2 h3)). Qed.
Lemma lem1043384 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h4 : y = (Nat.add y d) => @lem1043383 d' x y d h1 h2 h3) (fun h4 : False => @lem1041768 y d h3)). Qed.
Lemma lem1043385 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1043384 d' x y d h1 h2 h3) (@lem1041768 y d h3)). Qed.
Lemma lem1043386 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1042943 y d d' x h1 h2 h3) (fun h4 : False => @lem1041708 d' x h3)). Qed.
Lemma lem1043387 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1043386 y d d' x h1 h2 h3) (@lem1041708 d' x h3)). Qed.
Lemma lem1043388 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h4 : y = (Nat.add y d) => @lem1043385 d' x y d h1 h2 h3) (fun h4 : False => @lem1041536 y d h3)). Qed.
Lemma lem1043389 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1043388 d' x y d h1 h2 h3) (@lem1041536 y d h3)). Qed.
Lemma lem1043390 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1043387 y d d' x h1 h2 h3) (fun h4 : False => @lem1041430 d' x h3)). Qed.
Lemma lem1043391 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1043390 y d d' x h1 h2 h3) (@lem1041430 d' x h3)). Qed.
Lemma lem1043392 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : (y = (Nat.add y d)) = False.
Proof. exact (prop_ext (fun h4 : y = (Nat.add y d) => @lem1043389 d' x y d h1 h2 h3) (fun h4 : False => @lem1041536 y d h3)). Qed.
Lemma lem1043393 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : y = (Nat.add y d)) : False.
Proof. exact (EQ_MP (@lem1043392 d' x y d h1 h2 h3) (@lem1041536 y d h3)). Qed.
Lemma lem1043394 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1043391 y d d' x h1 h2 h3) (fun h4 : False => @lem1041430 d' x h3)). Qed.
Lemma lem1043395 (y : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term605 d' x y d) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1043394 y d d' x h1 h2 h3) (@lem1041430 d' x h3)). Qed.
Lemma lem1043396 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term605 d' x y d) : False.
Proof. exact (or_elim (@lem1041211 d' x y d h2) (fun h0 : (Nat.add x d') = x => @lem1043395 y d d' x h1 h2 h0) (fun h0 : y = (Nat.add y d) => @lem1043393 d' x y d h1 h2 h0)). Qed.
Lemma lem1043397 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term107) (h2 : term580 d' x y d) : False.
Proof. exact (or_elim (@lem1041018 d' x y d h2) (fun h0 : term608 d' x y d => @lem1042488 d' x y d h1 h0) (fun h0 : term605 d' x y d => @lem1043396 d' x y d h1 h0)). Qed.
Lemma lem1043398 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term181.
Proof. exact (fun h0 : term107 => @lem1043397 d' x y d h0 h1). Qed.
Lemma lem1043399 : term181 = term182.
Proof. exact (@lem69 term107). Qed.
Lemma lem1043400 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term182.
Proof. exact (EQ_MP (@lem1043399) (@lem1043398 d' x y d h1)). Qed.
Lemma lem1043401 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term185.
Proof. exact (fun h0 : term216 => @lem1043400 d' x y d h1). Qed.
Lemma lem1043402 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term188.
Proof. exact (fun h0 : term220 => @lem1043401 d' x y d h1). Qed.
Lemma lem1043403 (d' : nat) (x : nat) (y : nat) (d : nat) : term586 d' x y d.
Proof. exact (fun h0 : term580 d' x y d => @lem1043402 d' x y d h0). Qed.
Lemma lem1043408 (x : nat) (y : nat) (d : nat) : term590 x y d.
Proof. exact (fun d' : nat => @lem1043403 d' x y d). Qed.
Lemma lem1043413 (y : nat) (d : nat) : term594 y d.
Proof. exact (fun x : nat => @lem1043408 x y d). Qed.
Lemma lem1043418 (d : nat) : term598 d.
Proof. exact (fun y : nat => @lem1043413 y d). Qed.
Lemma lem1043423 : term602.
Proof. exact (fun d : nat => @lem1043418 d). Qed.
Lemma lem1043424 : term601.
Proof. exact (EQ_MP (@lem1040668) (@lem1043423)). Qed.
Lemma lem1043425 (d : nat) : term624 d.
Proof. exact (@lem1043424 d). Qed.
Lemma lem1043426 (d : nat) : (term624 d) = (term597 d).
Proof. exact (eq_refl (term624 d)). Qed.
Lemma lem1043427 (d : nat) : term597 d.
Proof. exact (EQ_MP (@lem1043426 d) (@lem1043425 d)). Qed.
Lemma lem1043428 (d : nat) (y : nat) : term625 d y.
Proof. exact (@lem1043427 d y). Qed.
Lemma lem1043429 (y : nat) (d : nat) : (term625 d y) = (term593 y d).
Proof. exact (eq_refl (term625 d y)). Qed.
Lemma lem1043430 (y : nat) (d : nat) : term593 y d.
Proof. exact (EQ_MP (@lem1043429 y d) (@lem1043428 d y)). Qed.
Lemma lem1043431 (y : nat) (d : nat) (x : nat) : term626 y d x.
Proof. exact (@lem1043430 y d x). Qed.
Lemma lem1043432 (x : nat) (y : nat) (d : nat) : (term626 y d x) = (term589 x y d).
Proof. exact (eq_refl (term626 y d x)). Qed.
Lemma lem1043433 (x : nat) (y : nat) (d : nat) : term589 x y d.
Proof. exact (EQ_MP (@lem1043432 x y d) (@lem1043431 y d x)). Qed.
Lemma lem1043434 (x : nat) (y : nat) (d : nat) (d' : nat) : term627 x y d d'.
Proof. exact (@lem1043433 x y d d'). Qed.
Lemma lem1043435 (d' : nat) (x : nat) (y : nat) (d : nat) : (term627 x y d d') = (term581 d' x y d).
Proof. exact (eq_refl (term627 x y d d')). Qed.
Lemma lem1043436 (d' : nat) (x : nat) (y : nat) (d : nat) : term581 d' x y d.
Proof. exact (EQ_MP (@lem1043435 d' x y d) (@lem1043434 x y d d')). Qed.
Lemma lem1043438 (d' : nat) (x : nat) (y : nat) (d : nat) : term581 d' x y d.
Proof. exact (@lem1040366 d' x y d (@lem1043436 d' x y d)). Qed.
Lemma lem1043439 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term187.
Proof. exact (@lem1043438 d' x y d (@lem1040351 d' x y d h1)). Qed.
Lemma lem1043440 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term184.
Proof. exact (@lem1043439 d' x y d h1 (@lem81820)). Qed.
Lemma lem1043441 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : term181.
Proof. exact (@lem1043440 d' x y d h1 (@lem77775)). Qed.
Lemma lem1043442 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : False.
Proof. exact (@lem1043441 d' x y d h1 (@lem1033477)). Qed.
Lemma lem1043443 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : (term580 d' x y d) = False.
Proof. exact (prop_ext (fun h2 : term580 d' x y d => @lem1043442 d' x y d h1) (fun h2 : False => @lem1040351 d' x y d h1)). Qed.
Lemma lem1043444 (d' : nat) (x : nat) (y : nat) (d : nat) (h1 : term580 d' x y d) : False.
Proof. exact (EQ_MP (@lem1043443 d' x y d h1) (@lem1040351 d' x y d h1)). Qed.
Lemma lem1043445 (d' : nat) (x : nat) (y : nat) (d : nat) : term579 d' x y d.
Proof. exact (fun h0 : term580 d' x y d => @lem1043444 d' x y d h0). Qed.
Lemma lem1043446 (d' : nat) (x : nat) (y : nat) (d : nat) : ((term58 d' x y d) = (term54 d' d x y)) = (term168 d' x y d).
Proof. exact (EQ_MP (@lem1040350 d' x y d) (@lem1043445 d' x y d)). Qed.
Lemma lem1043448 (p : Prop) : p = (term174 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1043449 (d' : nat) (x : nat) (d : nat) (z : nat) : (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)) = (term628 d' x d z).
Proof. exact (@lem1043448 (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z))). Qed.
Lemma lem1043450 (d' : nat) (x : nat) (d : nat) (z : nat) : (term628 d' x d z) = (((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z)).
Proof. exact (SYM (@lem1043449 d' x d z)). Qed.
Lemma lem1043451 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term629 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043454 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term630 d' x d z) : term630 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043455 (d' : nat) (x : nat) (d : nat) (z : nat) : term631 d' x d z.
Proof. exact (fun h0 : term630 d' x d z => @lem1043454 d' x d z h0). Qed.
Lemma lem1043456 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term631 d' x d z) : term631 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043457 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term630 d' x d z) : term630 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043458 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term630 d' x d z) (h2 : term631 d' x d z) : term630 d' x d z.
Proof. exact (@lem1043456 d' x d z h2 (@lem1043457 d' x d z h1)). Qed.
Lemma lem1043459 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term630 d' x d z) : term632 d' x d z.
Proof. exact (fun h0 : term631 d' x d z => @lem1043458 d' x d z h1 h0). Qed.
Lemma lem1043460 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term631 d' x d z) : term631 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043461 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term630 d' x d z) (h2 : term631 d' x d z) : term630 d' x d z.
Proof. exact (@lem1043459 d' x d z h1 (@lem1043460 d' x d z h2)). Qed.
Lemma lem1043462 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term631 d' x d z) : term631 d' x d z.
Proof. exact (fun h0 : term630 d' x d z => @lem1043461 d' x d z h0 h1). Qed.
Lemma lem1043463 (d' : nat) (x : nat) (d : nat) (z : nat) : term633 d' x d z.
Proof. exact (fun h0 : term631 d' x d z => @lem1043462 d' x d z h0). Qed.
Lemma lem1043466 (d' : nat) (x : nat) (d : nat) (z : nat) : term631 d' x d z.
Proof. exact (@lem1043463 d' x d z (@lem1043455 d' x d z)). Qed.
Lemma lem1043508 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1043509 : term181 = term182.
Proof. exact (@lem1043508 term107). Qed.
Lemma lem1043540 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1043541 : term184 = term185.
Proof. exact (MK_COMB (@lem1043540) (@lem1043509)). Qed.
Lemma lem1043544 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem1043545 : term187 = term188.
Proof. exact (MK_COMB (@lem1043544) (@lem1043541)). Qed.
Lemma lem1043548 (d' : nat) (x : nat) (d : nat) (z : nat) : (term634 d' x d z) = (term634 d' x d z).
Proof. exact (eq_refl (term634 d' x d z)). Qed.
Lemma lem1043549 (d' : nat) (x : nat) (d : nat) (z : nat) : (term630 d' x d z) = (term635 d' x d z).
Proof. exact (MK_COMB (@lem1043548 d' x d z) (@lem1043545)). Qed.
Lemma lem1043552 (x : nat) (d : nat) (z : nat) : (term636 x d z) = (term637 x d z).
Proof. exact (fun_ext (fun d' : nat => @lem1043549 d' x d z)). Qed.
Lemma lem1043553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043554 (x : nat) (d : nat) (z : nat) : (term638 x d z) = (term639 x d z).
Proof. exact (MK_COMB (@lem1043553) (@lem1043552 x d z)). Qed.
Lemma lem1043559 (d : nat) (z : nat) : (term640 d z) = (term641 d z).
Proof. exact (fun_ext (fun x : nat => @lem1043554 x d z)). Qed.
Lemma lem1043560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043561 (d : nat) (z : nat) : (term642 d z) = (term643 d z).
Proof. exact (MK_COMB (@lem1043560) (@lem1043559 d z)). Qed.
Lemma lem1043566 (z : nat) : (term644 z) = (term645 z).
Proof. exact (fun_ext (fun d : nat => @lem1043561 d z)). Qed.
Lemma lem1043567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043568 (z : nat) : (term646 z) = (term647 z).
Proof. exact (MK_COMB (@lem1043567) (@lem1043566 z)). Qed.
Lemma lem1043573 : term648 = term649.
Proof. exact (fun_ext (fun z : nat => @lem1043568 z)). Qed.
Lemma lem1043574 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043583 : term650 = term651.
Proof. exact (MK_COMB (@lem1043574) (@lem1043573)). Qed.
Lemma lem1043600 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term94 d e w x y z).
Proof. exact (eq_refl (term94 d e w x y z)). Qed.
Lemma lem1043601 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term207 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1043600 d e w x y z)). Qed.
Lemma lem1043602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043603 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term102 d e w x y).
Proof. exact (MK_COMB (@lem1043602) (@lem1043601 d e w x y)). Qed.
Lemma lem1043604 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term208 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1043603 d e w x y)). Qed.
Lemma lem1043605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043606 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term103 d e w x).
Proof. exact (MK_COMB (@lem1043605) (@lem1043604 d e w x)). Qed.
Lemma lem1043607 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term209 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1043606 d e w x)). Qed.
Lemma lem1043608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043609 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term104 d e w).
Proof. exact (MK_COMB (@lem1043608) (@lem1043607 d e w)). Qed.
Lemma lem1043610 (d : nat) (e : nat) : (term210 d e) = (term210 d e).
Proof. exact (fun_ext (fun w : nat => @lem1043609 d e w)). Qed.
Lemma lem1043611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043612 (d : nat) (e : nat) : (term105 d e) = (term105 d e).
Proof. exact (MK_COMB (@lem1043611) (@lem1043610 d e)). Qed.
Lemma lem1043613 (d : nat) : (term211 d) = (term211 d).
Proof. exact (fun_ext (fun e : nat => @lem1043612 d e)). Qed.
Lemma lem1043614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043615 (d : nat) : (term106 d) = (term106 d).
Proof. exact (MK_COMB (@lem1043614) (@lem1043613 d)). Qed.
Lemma lem1043616 : term212 = term212.
Proof. exact (fun_ext (fun d : nat => @lem1043615 d)). Qed.
Lemma lem1043617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043618 : term107 = term107.
Proof. exact (MK_COMB (@lem1043617) (@lem1043616)). Qed.
Lemma lem1043619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1043620 : term182 = term182.
Proof. exact (MK_COMB (@lem1043619) (@lem1043618)). Qed.
Lemma lem1043621 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1043622 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem1043621 n m)). Qed.
Lemma lem1043623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043624 (m : nat) : (term214 m) = (term214 m).
Proof. exact (MK_COMB (@lem1043623) (@lem1043622 m)). Qed.
Lemma lem1043625 : term215 = term215.
Proof. exact (fun_ext (fun m : nat => @lem1043624 m)). Qed.
Lemma lem1043626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043627 : term216 = term216.
Proof. exact (MK_COMB (@lem1043626) (@lem1043625)). Qed.
Lemma lem1043628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1043629 : term183 = term183.
Proof. exact (MK_COMB (@lem1043628) (@lem1043627)). Qed.
Lemma lem1043630 : term185 = term185.
Proof. exact (MK_COMB (@lem1043629) (@lem1043620)). Qed.
Lemma lem1043631 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem1043632 (m : nat) : (term217 m) = (term217 m).
Proof. exact (fun_ext (fun n : nat => @lem1043631 n m)). Qed.
Lemma lem1043633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043634 (m : nat) : (term218 m) = (term218 m).
Proof. exact (MK_COMB (@lem1043633) (@lem1043632 m)). Qed.
Lemma lem1043635 : term219 = term219.
Proof. exact (fun_ext (fun m : nat => @lem1043634 m)). Qed.
Lemma lem1043636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043637 : term220 = term220.
Proof. exact (MK_COMB (@lem1043636) (@lem1043635)). Qed.
Lemma lem1043638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1043639 : term186 = term186.
Proof. exact (MK_COMB (@lem1043638) (@lem1043637)). Qed.
Lemma lem1043640 : term188 = term188.
Proof. exact (MK_COMB (@lem1043639) (@lem1043630)). Qed.
Lemma lem1043653 (d' : nat) (x : nat) (d : nat) (z : nat) : (term634 d' x d z) = (term634 d' x d z).
Proof. exact (eq_refl (term634 d' x d z)). Qed.
Lemma lem1043654 (d' : nat) (x : nat) (d : nat) (z : nat) : (term635 d' x d z) = (term635 d' x d z).
Proof. exact (MK_COMB (@lem1043653 d' x d z) (@lem1043640)). Qed.
Lemma lem1043655 (x : nat) (d : nat) (z : nat) : (term637 x d z) = (term637 x d z).
Proof. exact (fun_ext (fun d' : nat => @lem1043654 d' x d z)). Qed.
Lemma lem1043656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043657 (x : nat) (d : nat) (z : nat) : (term639 x d z) = (term639 x d z).
Proof. exact (MK_COMB (@lem1043656) (@lem1043655 x d z)). Qed.
Lemma lem1043658 (d : nat) (z : nat) : (term641 d z) = (term641 d z).
Proof. exact (fun_ext (fun x : nat => @lem1043657 x d z)). Qed.
Lemma lem1043659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043660 (d : nat) (z : nat) : (term643 d z) = (term643 d z).
Proof. exact (MK_COMB (@lem1043659) (@lem1043658 d z)). Qed.
Lemma lem1043661 (z : nat) : (term645 z) = (term645 z).
Proof. exact (fun_ext (fun d : nat => @lem1043660 d z)). Qed.
Lemma lem1043662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043663 (z : nat) : (term647 z) = (term647 z).
Proof. exact (MK_COMB (@lem1043662) (@lem1043661 z)). Qed.
Lemma lem1043664 : term649 = term649.
Proof. exact (fun_ext (fun z : nat => @lem1043663 z)). Qed.
Lemma lem1043665 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043666 : term651 = term651.
Proof. exact (MK_COMB (@lem1043665) (@lem1043664)). Qed.
Lemma lem1043767 : term650 = term651.
Proof. exact (TRANS (@lem1043583) (@lem1043666)). Qed.
Lemma lem1043768 : term651 = term650.
Proof. exact (SYM (@lem1043767)). Qed.
Lemma lem1043769 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term629 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1043772 (h1 : term107) : term107.
Proof. exact (h1). Qed.
Lemma lem1043783 (d' : nat) (x : nat) (d : nat) (z : nat) : (term652 d' x d z) = (term653 d' x d z).
Proof. exact (@lem17160 ((Nat.add x d') = x) ((Nat.add z d) = z)). Qed.
Lemma lem1043789 (d' : nat) (x : nat) (d : nat) (z : nat) : (term654 d' x d z) = (term654 d' x d z).
Proof. exact (eq_refl (term654 d' x d z)). Qed.
Lemma lem1043791 (d' : nat) (x : nat) (z : nat) (d : nat) : (term655 d' x z d) = (term655 d' x z d).
Proof. exact (eq_refl (term655 d' x z d)). Qed.
Lemma lem1043792 (d' : nat) (x : nat) (d : nat) (z : nat) : (term656 d' x d z) = (term657 d' x d z).
Proof. exact (MK_COMB (@lem1043791 d' x z d) (@lem1043783 d' x d z)). Qed.
Lemma lem1043793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1043794 (d' : nat) (x : nat) (d : nat) (z : nat) : (term658 d' x d z) = (term659 d' x d z).
Proof. exact (MK_COMB (@lem1043793) (@lem1043792 d' x d z)). Qed.
Lemma lem1043795 (d' : nat) (x : nat) (d : nat) (z : nat) : (term660 d' x d z) = (term661 d' x d z).
Proof. exact (MK_COMB (@lem1043794 d' x d z) (@lem1043789 d' x d z)). Qed.
Lemma lem1043796 (d' : nat) (x : nat) (d : nat) (z : nat) : (term629 d' x d z) = (term660 d' x d z).
Proof. exact (@lem17646 ((term54 d' d x z) = (term58 d' x z d)) (term65 d' x d z)). Qed.
Lemma lem1043801 (d' : nat) (x : nat) (d : nat) (z : nat) : (term629 d' x d z) = (term661 d' x d z).
Proof. exact (TRANS (@lem1043796 d' x d z) (@lem1043795 d' x d z)). Qed.
Lemma lem1043849 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term231 w x d y z e) = (term232 w x d y z e).
Proof. exact (@lem17045 (w = (Nat.add x d)) (y = (Nat.add z e))). Qed.
Lemma lem1043860 (w : nat) (x : nat) (y : nat) (z : nat) : (term233 w x y z) = (term234 w x y z).
Proof. exact (@lem17160 (w = x) (y = z)). Qed.
Lemma lem1043866 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1043868 (w : nat) (z : nat) (x : nat) (y : nat) : (term236 w z x y) = (term236 w z x y).
Proof. exact (eq_refl (term236 w z x y)). Qed.
Lemma lem1043869 (w : nat) (x : nat) (y : nat) (z : nat) : (term237 w x y z) = (term238 w x y z).
Proof. exact (MK_COMB (@lem1043868 w z x y) (@lem1043860 w x y z)). Qed.
Lemma lem1043870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1043871 (w : nat) (x : nat) (y : nat) (z : nat) : (term239 w x y z) = (term240 w x y z).
Proof. exact (MK_COMB (@lem1043870) (@lem1043869 w x y z)). Qed.
Lemma lem1043872 (w : nat) (x : nat) (y : nat) (z : nat) : (term241 w x y z) = (term242 w x y z).
Proof. exact (MK_COMB (@lem1043871 w x y z) (@lem1043866 w x y z)). Qed.
Lemma lem1043873 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term241 w x y z).
Proof. exact (@lem17784 ((term53 w y x z) = (term53 w z x y)) (term64 w x y z)). Qed.
Lemma lem1043874 (w : nat) (x : nat) (y : nat) (z : nat) : (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z)) = (term242 w x y z).
Proof. exact (TRANS (@lem1043873 w x y z) (@lem1043872 w x y z)). Qed.
Lemma lem1043875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1043876 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term243 w x d y z e) = (term244 w x d y z e).
Proof. exact (MK_COMB (@lem1043875) (@lem1043849 w x d y z e)). Qed.
Lemma lem1043877 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term245 d e w x y z) = (term246 d e w x y z).
Proof. exact (MK_COMB (@lem1043876 w x d y z e) (@lem1043874 w x y z)). Qed.
Lemma lem1043878 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term245 d e w x y z).
Proof. exact (@lem17265 (term48 w x d y z e) (((term53 w y x z) = (term53 w z x y)) = (term64 w x y z))). Qed.
Lemma lem1043879 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term94 d e w x y z) = (term246 d e w x y z).
Proof. exact (TRANS (@lem1043878 d e w x y z) (@lem1043877 d e w x y z)). Qed.
Lemma lem1043880 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term207 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1043879 d e w x y z)). Qed.
Lemma lem1043881 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043882 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term102 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1043881) (@lem1043880 d e w x y)). Qed.
Lemma lem1043883 (d : nat) (e : nat) (w : nat) (x : nat) : (term208 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1043882 d e w x y)). Qed.
Lemma lem1043884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043885 (d : nat) (e : nat) (w : nat) (x : nat) : (term103 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1043884) (@lem1043883 d e w x)). Qed.
Lemma lem1043886 (d : nat) (e : nat) (w : nat) : (term209 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1043885 d e w x)). Qed.
Lemma lem1043887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043888 (d : nat) (e : nat) (w : nat) : (term104 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1043887) (@lem1043886 d e w)). Qed.
Lemma lem1043889 (d : nat) (e : nat) : (term210 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1043888 d e w)). Qed.
Lemma lem1043890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043891 (d : nat) (e : nat) : (term105 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1043890) (@lem1043889 d e)). Qed.
Lemma lem1043892 (d : nat) : (term211 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1043891 d e)). Qed.
Lemma lem1043893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043894 (d : nat) : (term106 d) = (term256 d).
Proof. exact (MK_COMB (@lem1043893) (@lem1043892 d)). Qed.
Lemma lem1043895 : term212 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1043894 d)). Qed.
Lemma lem1043896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1043969 : term107 = term258.
Proof. exact (MK_COMB (@lem1043896) (@lem1043895)). Qed.
Lemma lem1043970 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1043969) (@lem1043772 h1)). Qed.
Lemma lem1044118 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term661 d' x d z.
Proof. exact (EQ_MP (@lem1043801 d' x d z) (@lem1043769 d' x d z h1)). Qed.
Lemma lem1044285 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term246 d e w x y z).
Proof. exact (eq_refl (term246 d e w x y z)). Qed.
Lemma lem1044286 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term247 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1044285 d e w x y z)). Qed.
Lemma lem1044287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044288 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term248 d e w x y).
Proof. exact (MK_COMB (@lem1044287) (@lem1044286 d e w x y)). Qed.
Lemma lem1044289 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term249 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1044288 d e w x y)). Qed.
Lemma lem1044290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044291 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term250 d e w x).
Proof. exact (MK_COMB (@lem1044290) (@lem1044289 d e w x)). Qed.
Lemma lem1044292 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term251 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1044291 d e w x)). Qed.
Lemma lem1044293 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044294 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term252 d e w).
Proof. exact (MK_COMB (@lem1044293) (@lem1044292 d e w)). Qed.
Lemma lem1044295 (d : nat) (e : nat) : (term253 d e) = (term253 d e).
Proof. exact (fun_ext (fun w : nat => @lem1044294 d e w)). Qed.
Lemma lem1044296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044297 (d : nat) (e : nat) : (term254 d e) = (term254 d e).
Proof. exact (MK_COMB (@lem1044296) (@lem1044295 d e)). Qed.
Lemma lem1044298 (d : nat) : (term255 d) = (term255 d).
Proof. exact (fun_ext (fun e : nat => @lem1044297 d e)). Qed.
Lemma lem1044299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044300 (d : nat) : (term256 d) = (term256 d).
Proof. exact (MK_COMB (@lem1044299) (@lem1044298 d)). Qed.
Lemma lem1044301 : term257 = term257.
Proof. exact (fun_ext (fun d : nat => @lem1044300 d)). Qed.
Lemma lem1044302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044303 : term258 = term258.
Proof. exact (MK_COMB (@lem1044302) (@lem1044301)). Qed.
Lemma lem1044304 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem1044303) (@lem1043970 h1)). Qed.
Lemma lem1044305 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term657 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1044306 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term654 d' x d z.
Proof. exact (h1). Qed.
Lemma lem1044307 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term653 d' x d z.
Proof. exact (proj2 (@lem1044305 d' x d z h1)). Qed.
Lemma lem1044311 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term65 d' x d z.
Proof. exact (proj2 (@lem1044306 d' x d z h1)). Qed.
Lemma lem1044348 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1044365 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1044366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044367 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1044366) (@lem1044365 w x y z)). Qed.
Lemma lem1044368 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1044367 w x y z) (@lem1044348 w x y z)). Qed.
Lemma lem1044377 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1044378 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1044377 w x d y z e) (@lem1044368 w x y z)). Qed.
Lemma lem1044379 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1044380 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1044387 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1044388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044389 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1044388) (@lem1044387 d e w x y z)). Qed.
Lemma lem1044390 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1044389 d e w x y z) (@lem1044380 d e w x y z)). Qed.
Lemma lem1044391 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044379 d e w x y z) (@lem1044390 d e w x y z)). Qed.
Lemma lem1044392 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044378 d e w x y z) (@lem1044391 d e w x y z)). Qed.
Lemma lem1044393 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1044392 d e w x y z)). Qed.
Lemma lem1044394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044395 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1044394) (@lem1044393 d e w x y)). Qed.
Lemma lem1044396 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1044395 d e w x y)). Qed.
Lemma lem1044397 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044398 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1044397) (@lem1044396 d e w x)). Qed.
Lemma lem1044399 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1044398 d e w x)). Qed.
Lemma lem1044400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044401 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1044400) (@lem1044399 d e w)). Qed.
Lemma lem1044402 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1044401 d e w)). Qed.
Lemma lem1044403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044404 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1044403) (@lem1044402 d e)). Qed.
Lemma lem1044405 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1044404 d e)). Qed.
Lemma lem1044406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044407 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1044406) (@lem1044405 d)). Qed.
Lemma lem1044408 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1044407 d)). Qed.
Lemma lem1044409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044411 : term258 = term284.
Proof. exact (MK_COMB (@lem1044409) (@lem1044408)). Qed.
Lemma lem1044412 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1044411) (@lem1044304 h1)). Qed.
Lemma lem1044458 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1044475 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1044476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044477 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1044476) (@lem1044475 w x y z)). Qed.
Lemma lem1044478 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1044477 w x y z) (@lem1044458 w x y z)). Qed.
Lemma lem1044487 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1044488 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1044487 w x d y z e) (@lem1044478 w x y z)). Qed.
Lemma lem1044489 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1044490 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1044497 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1044498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044499 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1044498) (@lem1044497 d e w x y z)). Qed.
Lemma lem1044500 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1044499 d e w x y z) (@lem1044490 d e w x y z)). Qed.
Lemma lem1044501 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044489 d e w x y z) (@lem1044500 d e w x y z)). Qed.
Lemma lem1044502 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044488 d e w x y z) (@lem1044501 d e w x y z)). Qed.
Lemma lem1044503 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1044502 d e w x y z)). Qed.
Lemma lem1044504 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044505 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1044504) (@lem1044503 d e w x y)). Qed.
Lemma lem1044506 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1044505 d e w x y)). Qed.
Lemma lem1044507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044508 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1044507) (@lem1044506 d e w x)). Qed.
Lemma lem1044509 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1044508 d e w x)). Qed.
Lemma lem1044510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044511 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1044510) (@lem1044509 d e w)). Qed.
Lemma lem1044512 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1044511 d e w)). Qed.
Lemma lem1044513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044514 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1044513) (@lem1044512 d e)). Qed.
Lemma lem1044515 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1044514 d e)). Qed.
Lemma lem1044516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044517 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1044516) (@lem1044515 d)). Qed.
Lemma lem1044518 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1044517 d)). Qed.
Lemma lem1044519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044521 : term258 = term284.
Proof. exact (MK_COMB (@lem1044519) (@lem1044518)). Qed.
Lemma lem1044522 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1044521) (@lem1044304 h1)). Qed.
Lemma lem1044530 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1044564 (w : nat) (x : nat) (y : nat) (z : nat) : (term235 w x y z) = (term235 w x y z).
Proof. exact (eq_refl (term235 w x y z)). Qed.
Lemma lem1044581 (w : nat) (x : nat) (y : nat) (z : nat) : (term238 w x y z) = (term259 w x y z).
Proof. exact (@lem19490 (term260 w x) ((term53 w y x z) = (term53 w z x y)) (term260 y z)). Qed.
Lemma lem1044582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044583 (w : nat) (x : nat) (y : nat) (z : nat) : (term240 w x y z) = (term261 w x y z).
Proof. exact (MK_COMB (@lem1044582) (@lem1044581 w x y z)). Qed.
Lemma lem1044584 (w : nat) (x : nat) (y : nat) (z : nat) : (term242 w x y z) = (term262 w x y z).
Proof. exact (MK_COMB (@lem1044583 w x y z) (@lem1044564 w x y z)). Qed.
Lemma lem1044593 (w : nat) (x : nat) (d : nat) (y : nat) (z : nat) (e : nat) : (term244 w x d y z e) = (term244 w x d y z e).
Proof. exact (eq_refl (term244 w x d y z e)). Qed.
Lemma lem1044594 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term263 d e w x y z).
Proof. exact (MK_COMB (@lem1044593 w x d y z e) (@lem1044584 w x y z)). Qed.
Lemma lem1044595 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term264 d e w x y z).
Proof. exact (@lem19490 (term259 w x y z) (term232 w x d y z e) (term235 w x y z)). Qed.
Lemma lem1044596 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term265 d e w x y z) = (term265 d e w x y z).
Proof. exact (eq_refl (term265 d e w x y z)). Qed.
Lemma lem1044603 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term266 d e w x y z) = (term267 d e w x y z).
Proof. exact (@lem19490 (term268 z y w x) (term232 w x d y z e) (term269 w x y z)). Qed.
Lemma lem1044604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1044605 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term270 d e w x y z) = (term271 d e w x y z).
Proof. exact (MK_COMB (@lem1044604) (@lem1044603 d e w x y z)). Qed.
Lemma lem1044606 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term264 d e w x y z) = (term272 d e w x y z).
Proof. exact (MK_COMB (@lem1044605 d e w x y z) (@lem1044596 d e w x y z)). Qed.
Lemma lem1044607 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term263 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044595 d e w x y z) (@lem1044606 d e w x y z)). Qed.
Lemma lem1044608 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) (z : nat) : (term246 d e w x y z) = (term272 d e w x y z).
Proof. exact (TRANS (@lem1044594 d e w x y z) (@lem1044607 d e w x y z)). Qed.
Lemma lem1044609 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term247 d e w x y) = (term273 d e w x y).
Proof. exact (fun_ext (fun z : nat => @lem1044608 d e w x y z)). Qed.
Lemma lem1044610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044611 (d : nat) (e : nat) (w : nat) (x : nat) (y : nat) : (term248 d e w x y) = (term274 d e w x y).
Proof. exact (MK_COMB (@lem1044610) (@lem1044609 d e w x y)). Qed.
Lemma lem1044612 (d : nat) (e : nat) (w : nat) (x : nat) : (term249 d e w x) = (term275 d e w x).
Proof. exact (fun_ext (fun y : nat => @lem1044611 d e w x y)). Qed.
Lemma lem1044613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044614 (d : nat) (e : nat) (w : nat) (x : nat) : (term250 d e w x) = (term276 d e w x).
Proof. exact (MK_COMB (@lem1044613) (@lem1044612 d e w x)). Qed.
Lemma lem1044615 (d : nat) (e : nat) (w : nat) : (term251 d e w) = (term277 d e w).
Proof. exact (fun_ext (fun x : nat => @lem1044614 d e w x)). Qed.
Lemma lem1044616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044617 (d : nat) (e : nat) (w : nat) : (term252 d e w) = (term278 d e w).
Proof. exact (MK_COMB (@lem1044616) (@lem1044615 d e w)). Qed.
Lemma lem1044618 (d : nat) (e : nat) : (term253 d e) = (term279 d e).
Proof. exact (fun_ext (fun w : nat => @lem1044617 d e w)). Qed.
Lemma lem1044619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044620 (d : nat) (e : nat) : (term254 d e) = (term280 d e).
Proof. exact (MK_COMB (@lem1044619) (@lem1044618 d e)). Qed.
Lemma lem1044621 (d : nat) : (term255 d) = (term281 d).
Proof. exact (fun_ext (fun e : nat => @lem1044620 d e)). Qed.
Lemma lem1044622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044623 (d : nat) : (term256 d) = (term282 d).
Proof. exact (MK_COMB (@lem1044622) (@lem1044621 d)). Qed.
Lemma lem1044624 : term257 = term283.
Proof. exact (fun_ext (fun d : nat => @lem1044623 d)). Qed.
Lemma lem1044625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1044627 : term258 = term284.
Proof. exact (MK_COMB (@lem1044625) (@lem1044624)). Qed.
Lemma lem1044628 (h1 : term107) : term284.
Proof. exact (EQ_MP (@lem1044627) (@lem1044304 h1)). Qed.
Lemma lem1044636 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1044649 (_17270 : nat) (h1 : term107) : term287 _17270.
Proof. exact (@lem1044412 h1 _17270). Qed.
Lemma lem1044650 (_17270 : nat) : (term287 _17270) = (term282 _17270).
Proof. exact (eq_refl (term287 _17270)). Qed.
Lemma lem1044651 (_17270 : nat) (h1 : term107) : term282 _17270.
Proof. exact (EQ_MP (@lem1044650 _17270) (@lem1044649 _17270 h1)). Qed.
Lemma lem1044652 (_17270 : nat) (_17271 : nat) (h1 : term107) : term288 _17270 _17271.
Proof. exact (@lem1044651 _17270 h1 _17271). Qed.
Lemma lem1044653 (_17270 : nat) (_17271 : nat) : (term288 _17270 _17271) = (term280 _17270 _17271).
Proof. exact (eq_refl (term288 _17270 _17271)). Qed.
Lemma lem1044654 (_17270 : nat) (_17271 : nat) (h1 : term107) : term280 _17270 _17271.
Proof. exact (EQ_MP (@lem1044653 _17270 _17271) (@lem1044652 _17270 _17271 h1)). Qed.
Lemma lem1044655 (_17270 : nat) (_17271 : nat) (_17272 : nat) (h1 : term107) : term289 _17270 _17271 _17272.
Proof. exact (@lem1044654 _17270 _17271 h1 _17272). Qed.
Lemma lem1044656 (_17270 : nat) (_17271 : nat) (_17272 : nat) : (term289 _17270 _17271 _17272) = (term278 _17270 _17271 _17272).
Proof. exact (eq_refl (term289 _17270 _17271 _17272)). Qed.
Lemma lem1044657 (_17270 : nat) (_17271 : nat) (_17272 : nat) (h1 : term107) : term278 _17270 _17271 _17272.
Proof. exact (EQ_MP (@lem1044656 _17270 _17271 _17272) (@lem1044655 _17270 _17271 _17272 h1)). Qed.
Lemma lem1044658 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (h1 : term107) : term290 _17270 _17271 _17272 _17273.
Proof. exact (@lem1044657 _17270 _17271 _17272 h1 _17273). Qed.
Lemma lem1044659 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) : (term290 _17270 _17271 _17272 _17273) = (term276 _17270 _17271 _17272 _17273).
Proof. exact (eq_refl (term290 _17270 _17271 _17272 _17273)). Qed.
Lemma lem1044660 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (h1 : term107) : term276 _17270 _17271 _17272 _17273.
Proof. exact (EQ_MP (@lem1044659 _17270 _17271 _17272 _17273) (@lem1044658 _17270 _17271 _17272 _17273 h1)). Qed.
Lemma lem1044661 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (h1 : term107) : term291 _17270 _17271 _17272 _17273 _17274.
Proof. exact (@lem1044660 _17270 _17271 _17272 _17273 h1 _17274). Qed.
Lemma lem1044662 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) : (term291 _17270 _17271 _17272 _17273 _17274) = (term274 _17270 _17271 _17272 _17273 _17274).
Proof. exact (eq_refl (term291 _17270 _17271 _17272 _17273 _17274)). Qed.
Lemma lem1044663 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (h1 : term107) : term274 _17270 _17271 _17272 _17273 _17274.
Proof. exact (EQ_MP (@lem1044662 _17270 _17271 _17272 _17273 _17274) (@lem1044661 _17270 _17271 _17272 _17273 _17274 h1)). Qed.
Lemma lem1044664 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) (h1 : term107) : term292 _17270 _17271 _17272 _17273 _17274 _17275.
Proof. exact (@lem1044663 _17270 _17271 _17272 _17273 _17274 h1 _17275). Qed.
Lemma lem1044665 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term292 _17270 _17271 _17272 _17273 _17274 _17275) = (term272 _17270 _17271 _17272 _17273 _17274 _17275).
Proof. exact (eq_refl (term292 _17270 _17271 _17272 _17273 _17274 _17275)). Qed.
Lemma lem1044666 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) (h1 : term107) : term272 _17270 _17271 _17272 _17273 _17274 _17275.
Proof. exact (EQ_MP (@lem1044665 _17270 _17271 _17272 _17273 _17274 _17275) (@lem1044664 _17270 _17271 _17272 _17273 _17274 _17275 h1)). Qed.
Lemma lem1044679 (_17280 : nat) (h1 : term107) : term287 _17280.
Proof. exact (@lem1044522 h1 _17280). Qed.
Lemma lem1044680 (_17280 : nat) : (term287 _17280) = (term282 _17280).
Proof. exact (eq_refl (term287 _17280)). Qed.
Lemma lem1044681 (_17280 : nat) (h1 : term107) : term282 _17280.
Proof. exact (EQ_MP (@lem1044680 _17280) (@lem1044679 _17280 h1)). Qed.
Lemma lem1044682 (_17280 : nat) (_17281 : nat) (h1 : term107) : term288 _17280 _17281.
Proof. exact (@lem1044681 _17280 h1 _17281). Qed.
Lemma lem1044683 (_17280 : nat) (_17281 : nat) : (term288 _17280 _17281) = (term280 _17280 _17281).
Proof. exact (eq_refl (term288 _17280 _17281)). Qed.
Lemma lem1044684 (_17280 : nat) (_17281 : nat) (h1 : term107) : term280 _17280 _17281.
Proof. exact (EQ_MP (@lem1044683 _17280 _17281) (@lem1044682 _17280 _17281 h1)). Qed.
Lemma lem1044685 (_17280 : nat) (_17281 : nat) (_17282 : nat) (h1 : term107) : term289 _17280 _17281 _17282.
Proof. exact (@lem1044684 _17280 _17281 h1 _17282). Qed.
Lemma lem1044686 (_17280 : nat) (_17281 : nat) (_17282 : nat) : (term289 _17280 _17281 _17282) = (term278 _17280 _17281 _17282).
Proof. exact (eq_refl (term289 _17280 _17281 _17282)). Qed.
Lemma lem1044687 (_17280 : nat) (_17281 : nat) (_17282 : nat) (h1 : term107) : term278 _17280 _17281 _17282.
Proof. exact (EQ_MP (@lem1044686 _17280 _17281 _17282) (@lem1044685 _17280 _17281 _17282 h1)). Qed.
Lemma lem1044688 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (h1 : term107) : term290 _17280 _17281 _17282 _17283.
Proof. exact (@lem1044687 _17280 _17281 _17282 h1 _17283). Qed.
Lemma lem1044689 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term290 _17280 _17281 _17282 _17283) = (term276 _17280 _17281 _17282 _17283).
Proof. exact (eq_refl (term290 _17280 _17281 _17282 _17283)). Qed.
Lemma lem1044690 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (h1 : term107) : term276 _17280 _17281 _17282 _17283.
Proof. exact (EQ_MP (@lem1044689 _17280 _17281 _17282 _17283) (@lem1044688 _17280 _17281 _17282 _17283 h1)). Qed.
Lemma lem1044691 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (h1 : term107) : term291 _17280 _17281 _17282 _17283 _17284.
Proof. exact (@lem1044690 _17280 _17281 _17282 _17283 h1 _17284). Qed.
Lemma lem1044692 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) : (term291 _17280 _17281 _17282 _17283 _17284) = (term274 _17280 _17281 _17282 _17283 _17284).
Proof. exact (eq_refl (term291 _17280 _17281 _17282 _17283 _17284)). Qed.
Lemma lem1044693 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (h1 : term107) : term274 _17280 _17281 _17282 _17283 _17284.
Proof. exact (EQ_MP (@lem1044692 _17280 _17281 _17282 _17283 _17284) (@lem1044691 _17280 _17281 _17282 _17283 _17284 h1)). Qed.
Lemma lem1044694 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (h1 : term107) : term292 _17280 _17281 _17282 _17283 _17284 _17285.
Proof. exact (@lem1044693 _17280 _17281 _17282 _17283 _17284 h1 _17285). Qed.
Lemma lem1044695 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) : (term292 _17280 _17281 _17282 _17283 _17284 _17285) = (term272 _17280 _17281 _17282 _17283 _17284 _17285).
Proof. exact (eq_refl (term292 _17280 _17281 _17282 _17283 _17284 _17285)). Qed.
Lemma lem1044696 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (h1 : term107) : term272 _17280 _17281 _17282 _17283 _17284 _17285.
Proof. exact (EQ_MP (@lem1044695 _17280 _17281 _17282 _17283 _17284 _17285) (@lem1044694 _17280 _17281 _17282 _17283 _17284 _17285 h1)). Qed.
Lemma lem1044709 (_17290 : nat) (h1 : term107) : term287 _17290.
Proof. exact (@lem1044628 h1 _17290). Qed.
Lemma lem1044710 (_17290 : nat) : (term287 _17290) = (term282 _17290).
Proof. exact (eq_refl (term287 _17290)). Qed.
Lemma lem1044711 (_17290 : nat) (h1 : term107) : term282 _17290.
Proof. exact (EQ_MP (@lem1044710 _17290) (@lem1044709 _17290 h1)). Qed.
Lemma lem1044712 (_17290 : nat) (_17291 : nat) (h1 : term107) : term288 _17290 _17291.
Proof. exact (@lem1044711 _17290 h1 _17291). Qed.
Lemma lem1044713 (_17290 : nat) (_17291 : nat) : (term288 _17290 _17291) = (term280 _17290 _17291).
Proof. exact (eq_refl (term288 _17290 _17291)). Qed.
Lemma lem1044714 (_17290 : nat) (_17291 : nat) (h1 : term107) : term280 _17290 _17291.
Proof. exact (EQ_MP (@lem1044713 _17290 _17291) (@lem1044712 _17290 _17291 h1)). Qed.
Lemma lem1044715 (_17290 : nat) (_17291 : nat) (_17292 : nat) (h1 : term107) : term289 _17290 _17291 _17292.
Proof. exact (@lem1044714 _17290 _17291 h1 _17292). Qed.
Lemma lem1044716 (_17290 : nat) (_17291 : nat) (_17292 : nat) : (term289 _17290 _17291 _17292) = (term278 _17290 _17291 _17292).
Proof. exact (eq_refl (term289 _17290 _17291 _17292)). Qed.
Lemma lem1044717 (_17290 : nat) (_17291 : nat) (_17292 : nat) (h1 : term107) : term278 _17290 _17291 _17292.
Proof. exact (EQ_MP (@lem1044716 _17290 _17291 _17292) (@lem1044715 _17290 _17291 _17292 h1)). Qed.
Lemma lem1044718 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (h1 : term107) : term290 _17290 _17291 _17292 _17293.
Proof. exact (@lem1044717 _17290 _17291 _17292 h1 _17293). Qed.
Lemma lem1044719 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) : (term290 _17290 _17291 _17292 _17293) = (term276 _17290 _17291 _17292 _17293).
Proof. exact (eq_refl (term290 _17290 _17291 _17292 _17293)). Qed.
Lemma lem1044720 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (h1 : term107) : term276 _17290 _17291 _17292 _17293.
Proof. exact (EQ_MP (@lem1044719 _17290 _17291 _17292 _17293) (@lem1044718 _17290 _17291 _17292 _17293 h1)). Qed.
Lemma lem1044721 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (h1 : term107) : term291 _17290 _17291 _17292 _17293 _17294.
Proof. exact (@lem1044720 _17290 _17291 _17292 _17293 h1 _17294). Qed.
Lemma lem1044722 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) : (term291 _17290 _17291 _17292 _17293 _17294) = (term274 _17290 _17291 _17292 _17293 _17294).
Proof. exact (eq_refl (term291 _17290 _17291 _17292 _17293 _17294)). Qed.
Lemma lem1044723 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (h1 : term107) : term274 _17290 _17291 _17292 _17293 _17294.
Proof. exact (EQ_MP (@lem1044722 _17290 _17291 _17292 _17293 _17294) (@lem1044721 _17290 _17291 _17292 _17293 _17294 h1)). Qed.
Lemma lem1044724 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term292 _17290 _17291 _17292 _17293 _17294 _17295.
Proof. exact (@lem1044723 _17290 _17291 _17292 _17293 _17294 h1 _17295). Qed.
Lemma lem1044725 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) : (term292 _17290 _17291 _17292 _17293 _17294 _17295) = (term272 _17290 _17291 _17292 _17293 _17294 _17295).
Proof. exact (eq_refl (term292 _17290 _17291 _17292 _17293 _17294 _17295)). Qed.
Lemma lem1044726 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term272 _17290 _17291 _17292 _17293 _17294 _17295.
Proof. exact (EQ_MP (@lem1044725 _17290 _17291 _17292 _17293 _17294 _17295) (@lem1044724 _17290 _17291 _17292 _17293 _17294 _17295 h1)). Qed.
Lemma lem1044727 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) (h1 : term107) : term265 _17270 _17271 _17272 _17273 _17274 _17275.
Proof. exact (proj2 (@lem1044666 _17270 _17271 _17272 _17273 _17274 _17275 h1)). Qed.
Lemma lem1044732 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (h1 : term107) : term267 _17280 _17281 _17282 _17283 _17284 _17285.
Proof. exact (proj1 (@lem1044696 _17280 _17281 _17282 _17283 _17284 _17285 h1)). Qed.
Lemma lem1044734 (_17280 : nat) (_17281 : nat) (_17285 : nat) (_17284 : nat) (_17282 : nat) (_17283 : nat) (h1 : term107) : term293 _17280 _17281 _17285 _17284 _17282 _17283.
Proof. exact (proj1 (@lem1044732 _17280 _17281 _17282 _17283 _17284 _17285 h1)). Qed.
Lemma lem1044736 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term267 _17290 _17291 _17292 _17293 _17294 _17295.
Proof. exact (proj1 (@lem1044726 _17290 _17291 _17292 _17293 _17294 _17295 h1)). Qed.
Lemma lem1044737 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term536 _17290 _17291 _17292 _17293 _17294 _17295.
Proof. exact (proj2 (@lem1044736 _17290 _17291 _17292 _17293 _17294 _17295 h1)). Qed.
Lemma lem1044748 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term349 d z.
Proof. exact (proj2 (@lem1044307 d' x d z h1)). Qed.
Lemma lem1044767 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term265 _17270 _17271 _17272 _17273 _17274 _17275) = (term295 _17270 _17271 _17272 _17273 _17274 _17275).
Proof. exact (@lem1033471 (term296 _17272 _17273 _17270) (term296 _17274 _17275 _17271) (term235 _17272 _17273 _17274 _17275)). Qed.
Lemma lem1044768 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) (h1 : term107) : term295 _17270 _17271 _17272 _17273 _17274 _17275.
Proof. exact (EQ_MP (@lem1044767 _17270 _17271 _17272 _17273 _17274 _17275) (@lem1044727 _17270 _17271 _17272 _17273 _17274 _17275 h1)). Qed.
Lemma lem1044806 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term337 d' x z d.
Proof. exact (proj1 (@lem1044306 d' x d z h1)). Qed.
Lemma lem1044808 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1044843 (_17280 : nat) (_17281 : nat) (_17285 : nat) (_17284 : nat) (_17282 : nat) (_17283 : nat) : (term293 _17280 _17281 _17285 _17284 _17282 _17283) = (term298 _17280 _17281 _17285 _17284 _17282 _17283).
Proof. exact (@lem1033471 (term296 _17282 _17283 _17280) (term296 _17284 _17285 _17281) (term268 _17285 _17284 _17282 _17283)). Qed.
Lemma lem1044844 (_17280 : nat) (_17281 : nat) (_17285 : nat) (_17284 : nat) (_17282 : nat) (_17283 : nat) (h1 : term107) : term298 _17280 _17281 _17285 _17284 _17282 _17283.
Proof. exact (EQ_MP (@lem1044843 _17280 _17281 _17285 _17284 _17282 _17283) (@lem1044734 _17280 _17281 _17285 _17284 _17282 _17283 h1)). Qed.
Lemma lem1044866 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term337 d' x z d.
Proof. exact (proj1 (@lem1044306 d' x d z h1)). Qed.
Lemma lem1044868 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1044919 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) : (term536 _17290 _17291 _17292 _17293 _17294 _17295) = (term538 _17290 _17291 _17292 _17293 _17294 _17295).
Proof. exact (@lem1033471 (term296 _17292 _17293 _17290) (term296 _17294 _17295 _17291) (term269 _17292 _17293 _17294 _17295)). Qed.
Lemma lem1044920 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term538 _17290 _17291 _17292 _17293 _17294 _17295.
Proof. exact (EQ_MP (@lem1044919 _17290 _17291 _17292 _17293 _17294 _17295) (@lem1044737 _17290 _17291 _17292 _17293 _17294 _17295 h1)). Qed.
Lemma lem1044954 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1044955 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1044954 (Nat.add x d')). Qed.
Lemma lem1044956 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1044955 x d'). Qed.
Lemma lem1044958 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1044959 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1044958 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1044960 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1044959 x d') (@lem1044956 x d')). Qed.
Lemma lem1044962 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1044963 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1044962 (Nat.add z d)). Qed.
Lemma lem1044964 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1044963 z d). Qed.
Lemma lem1044966 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1044967 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1044966 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1044968 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1044967 z d) (@lem1044964 z d)). Qed.
Lemma lem1044970 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (proj1 (@lem1044305 d' x d z h1)). Qed.
Lemma lem1044971 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term336 d' x z d.
Proof. exact (fun h0 : term337 d' x z d => @lem1044970 d' x d z h1). Qed.
Lemma lem1044973 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1044974 (d' : nat) (x : nat) (z : nat) (d : nat) : (term336 d' x z d) = ((term54 d' d x z) = (term58 d' x z d)).
Proof. exact (@lem1044973 ((term54 d' d x z) = (term58 d' x z d))). Qed.
Lemma lem1044975 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (EQ_MP (@lem1044974 d' x z d) (@lem1044971 d' x d z h1)). Qed.
Lemma lem1044977 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term349 d' x.
Proof. exact (proj1 (@lem1044307 d' x d z h1)). Qed.
Lemma lem1044978 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term350 d' x.
Proof. exact (fun h0 : (Nat.add x d') = x => @lem1044977 d' x d z h1). Qed.
Lemma lem1044980 (p : Prop) : (term339 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1044981 (d' : nat) (x : nat) : (term350 d' x) = (term349 d' x).
Proof. exact (@lem1044980 ((Nat.add x d') = x)). Qed.
Lemma lem1044982 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term349 d' x.
Proof. exact (EQ_MP (@lem1044981 d' x) (@lem1044978 d' x d z h1)). Qed.
Lemma lem1045012 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045013 (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term235 _17272 _17273 _17274 _17275) = (term351 _17272 _17273 _17274 _17275).
Proof. exact (@lem1045012 (_17272 = _17273) (term352 _17272 _17275 _17273 _17274) (_17274 = _17275)). Qed.
Lemma lem1045029 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045030 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term353 _17272 _17273 _17274 _17275) = (term354 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045029 (_17274 = _17275) (term352 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045040 (_17272 : nat) (_17273 : nat) : (term62 _17272 _17273) = (term62 _17272 _17273).
Proof. exact (eq_refl (term62 _17272 _17273)). Qed.
Lemma lem1045041 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term351 _17272 _17273 _17274 _17275) = (term355 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045040 _17272 _17273) (@lem1045030 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045052 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term235 _17272 _17273 _17274 _17275) = (term355 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045013 _17272 _17273 _17274 _17275) (@lem1045041 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045053 (_17274 : nat) (_17275 : nat) (_17271 : nat) : (term356 _17274 _17275 _17271) = (term356 _17274 _17275 _17271).
Proof. exact (eq_refl (term356 _17274 _17275 _17271)). Qed.
Lemma lem1045054 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term357 _17271 _17272 _17273 _17274 _17275) = (term358 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045053 _17274 _17275 _17271) (@lem1045052 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045058 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045059 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term358 _17271 _17272 _17275 _17273 _17274) = (term359 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045058 (_17272 = _17273) (term296 _17274 _17275 _17271) (term354 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045075 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045076 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term360 _17271 _17272 _17275 _17273 _17274) = (term361 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045075 (_17274 = _17275) (term296 _17274 _17275 _17271) (term352 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045098 (_17272 : nat) (_17273 : nat) : (term62 _17272 _17273) = (term62 _17272 _17273).
Proof. exact (eq_refl (term62 _17272 _17273)). Qed.
Lemma lem1045099 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term359 _17271 _17272 _17275 _17273 _17274) = (term362 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045098 _17272 _17273) (@lem1045076 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045110 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term358 _17271 _17272 _17275 _17273 _17274) = (term362 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045059 _17271 _17272 _17275 _17273 _17274) (@lem1045099 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045111 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term357 _17271 _17272 _17273 _17274 _17275) = (term362 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045054 _17271 _17272 _17275 _17273 _17274) (@lem1045110 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045112 (_17272 : nat) (_17273 : nat) (_17270 : nat) : (term356 _17272 _17273 _17270) = (term356 _17272 _17273 _17270).
Proof. exact (eq_refl (term356 _17272 _17273 _17270)). Qed.
Lemma lem1045113 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term363 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045112 _17272 _17273 _17270) (@lem1045111 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045117 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045118 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term363 _17270 _17271 _17272 _17275 _17273 _17274) = (term364 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045117 (_17272 = _17273) (term296 _17272 _17273 _17270) (term361 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045134 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045135 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term365 _17270 _17271 _17272 _17275 _17273 _17274) = (term366 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045134 (_17274 = _17275) (term296 _17272 _17273 _17270) (term367 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045169 (_17272 : nat) (_17273 : nat) : (term62 _17272 _17273) = (term62 _17272 _17273).
Proof. exact (eq_refl (term62 _17272 _17273)). Qed.
Lemma lem1045170 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term364 _17270 _17271 _17272 _17275 _17273 _17274) = (term368 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045169 _17272 _17273) (@lem1045135 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045181 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term363 _17270 _17271 _17272 _17275 _17273 _17274) = (term368 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045118 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045170 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045182 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term368 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045113 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045181 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1045184 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term369 _17270 _17271 _17272 _17273 _17274 _17275) = (term370 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045183) (@lem1045182 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045224 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045225 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term371 _17275 _17274 _17272 _17273) = (term372 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045224 (_17272 = _17273) (term352 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045235 (_17274 : nat) (_17275 : nat) (_17271 : nat) : (term356 _17274 _17275 _17271) = (term356 _17274 _17275 _17271).
Proof. exact (eq_refl (term356 _17274 _17275 _17271)). Qed.
Lemma lem1045236 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term373 _17271 _17275 _17274 _17272 _17273) = (term374 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045235 _17274 _17275 _17271) (@lem1045225 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045240 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045241 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term374 _17271 _17272 _17275 _17273 _17274) = (term375 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045240 (_17272 = _17273) (term296 _17274 _17275 _17271) (term352 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045263 (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term373 _17271 _17275 _17274 _17272 _17273) = (term375 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045236 _17271 _17272 _17275 _17273 _17274) (@lem1045241 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045264 (_17272 : nat) (_17273 : nat) (_17270 : nat) : (term356 _17272 _17273 _17270) = (term356 _17272 _17273 _17270).
Proof. exact (eq_refl (term356 _17272 _17273 _17270)). Qed.
Lemma lem1045265 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term376 _17270 _17271 _17275 _17274 _17272 _17273) = (term377 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045264 _17272 _17273 _17270) (@lem1045263 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045269 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045270 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term377 _17270 _17271 _17272 _17275 _17273 _17274) = (term378 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045269 (_17272 = _17273) (term296 _17272 _17273 _17270) (term367 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045304 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term376 _17270 _17271 _17275 _17274 _17272 _17273) = (term378 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045265 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045270 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045305 (_17274 : nat) (_17275 : nat) : (term62 _17274 _17275) = (term62 _17274 _17275).
Proof. exact (eq_refl (term62 _17274 _17275)). Qed.
Lemma lem1045306 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term379 _17270 _17271 _17275 _17274 _17272 _17273) = (term380 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045305 _17274 _17275) (@lem1045304 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045310 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045311 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term380 _17270 _17271 _17272 _17275 _17273 _17274) = (term368 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (@lem1045310 (_17272 = _17273) (_17274 = _17275) (term381 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045357 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term379 _17270 _17271 _17275 _17274 _17272 _17273) = (term368 _17270 _17271 _17272 _17275 _17273 _17274).
Proof. exact (TRANS (@lem1045306 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045311 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045358 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : ((term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term379 _17270 _17271 _17275 _17274 _17272 _17273)) = ((term368 _17270 _17271 _17272 _17275 _17273 _17274) = (term368 _17270 _17271 _17272 _17275 _17273 _17274)).
Proof. exact (MK_COMB (@lem1045184 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045357 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1045361 (x : Prop) : (x = x) = True.
Proof. exact (@lem1045360 Prop x). Qed.
Lemma lem1045362 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : ((term368 _17270 _17271 _17272 _17275 _17273 _17274) = (term368 _17270 _17271 _17272 _17275 _17273 _17274)) = True.
Proof. exact (@lem1045361 (term368 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045363 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : ((term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term379 _17270 _17271 _17275 _17274 _17272 _17273)) = True.
Proof. exact (TRANS (@lem1045358 _17270 _17271 _17272 _17275 _17273 _17274) (@lem1045362 _17270 _17271 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045364 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : True = ((term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term379 _17270 _17271 _17275 _17274 _17272 _17273)).
Proof. exact (SYM (@lem1045363 _17270 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045365 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term295 _17270 _17271 _17272 _17273 _17274 _17275) = (term379 _17270 _17271 _17275 _17274 _17272 _17273).
Proof. exact (EQ_MP (@lem1045364 _17270 _17271 _17275 _17274 _17272 _17273) (@lem0)). Qed.
Lemma lem1045366 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) (h1 : term107) : term379 _17270 _17271 _17275 _17274 _17272 _17273.
Proof. exact (EQ_MP (@lem1045365 _17270 _17271 _17275 _17274 _17272 _17273) (@lem1044768 _17270 _17271 _17272 _17273 _17274 _17275 h1)). Qed.
Lemma lem1045368 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1045369 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term379 _17270 _17271 _17275 _17274 _17272 _17273) = (term382 _17270 _17271 _17272 _17273 _17274 _17275).
Proof. exact (@lem1045368 (term376 _17270 _17271 _17275 _17274 _17272 _17273) (_17274 = _17275)). Qed.
Lemma lem1045371 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045372 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term383 _17270 _17271 _17275 _17274 _17272 _17273) = (term384 _17270 _17271 _17275 _17274 _17272 _17273).
Proof. exact (@lem1045371 (term296 _17272 _17273 _17270) (term373 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045374 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045375 (_17272 : nat) (_17273 : nat) (_17270 : nat) : (term385 _17272 _17273 _17270) = (_17272 = (Nat.add _17273 _17270)).
Proof. exact (@lem1045374 (_17272 = (Nat.add _17273 _17270))). Qed.
Lemma lem1045376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045377 (_17272 : nat) (_17273 : nat) (_17270 : nat) : (term386 _17272 _17273 _17270) = (term387 _17272 _17273 _17270).
Proof. exact (MK_COMB (@lem1045376) (@lem1045375 _17272 _17273 _17270)). Qed.
Lemma lem1045379 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045380 (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term388 _17271 _17275 _17274 _17272 _17273) = (term389 _17271 _17275 _17274 _17272 _17273).
Proof. exact (@lem1045379 (term296 _17274 _17275 _17271) (term371 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045382 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045383 (_17274 : nat) (_17275 : nat) (_17271 : nat) : (term385 _17274 _17275 _17271) = (_17274 = (Nat.add _17275 _17271)).
Proof. exact (@lem1045382 (_17274 = (Nat.add _17275 _17271))). Qed.
Lemma lem1045384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045385 (_17274 : nat) (_17275 : nat) (_17271 : nat) : (term386 _17274 _17275 _17271) = (term387 _17274 _17275 _17271).
Proof. exact (MK_COMB (@lem1045384) (@lem1045383 _17274 _17275 _17271)). Qed.
Lemma lem1045387 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045388 (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term390 _17275 _17274 _17272 _17273) = (term391 _17275 _17274 _17272 _17273).
Proof. exact (@lem1045387 (term352 _17272 _17275 _17273 _17274) (_17272 = _17273)). Qed.
Lemma lem1045390 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045391 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term392 _17272 _17275 _17273 _17274) = ((term53 _17272 _17274 _17273 _17275) = (term53 _17272 _17275 _17273 _17274)).
Proof. exact (@lem1045390 ((term53 _17272 _17274 _17273 _17275) = (term53 _17272 _17275 _17273 _17274))). Qed.
Lemma lem1045392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045393 (_17272 : nat) (_17275 : nat) (_17273 : nat) (_17274 : nat) : (term393 _17272 _17275 _17273 _17274) = (term394 _17272 _17275 _17273 _17274).
Proof. exact (MK_COMB (@lem1045392) (@lem1045391 _17272 _17275 _17273 _17274)). Qed.
Lemma lem1045394 (_17272 : nat) (_17273 : nat) : (term260 _17272 _17273) = (term260 _17272 _17273).
Proof. exact (eq_refl (term260 _17272 _17273)). Qed.
Lemma lem1045395 (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term391 _17275 _17274 _17272 _17273) = (term395 _17275 _17274 _17272 _17273).
Proof. exact (MK_COMB (@lem1045393 _17272 _17275 _17273 _17274) (@lem1045394 _17272 _17273)). Qed.
Lemma lem1045396 (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term390 _17275 _17274 _17272 _17273) = (term395 _17275 _17274 _17272 _17273).
Proof. exact (TRANS (@lem1045388 _17275 _17274 _17272 _17273) (@lem1045395 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045397 (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term389 _17271 _17275 _17274 _17272 _17273) = (term396 _17271 _17275 _17274 _17272 _17273).
Proof. exact (MK_COMB (@lem1045385 _17274 _17275 _17271) (@lem1045396 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045398 (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term388 _17271 _17275 _17274 _17272 _17273) = (term396 _17271 _17275 _17274 _17272 _17273).
Proof. exact (TRANS (@lem1045380 _17271 _17275 _17274 _17272 _17273) (@lem1045397 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045399 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term384 _17270 _17271 _17275 _17274 _17272 _17273) = (term397 _17270 _17271 _17275 _17274 _17272 _17273).
Proof. exact (MK_COMB (@lem1045377 _17272 _17273 _17270) (@lem1045398 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045400 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term383 _17270 _17271 _17275 _17274 _17272 _17273) = (term397 _17270 _17271 _17275 _17274 _17272 _17273).
Proof. exact (TRANS (@lem1045372 _17270 _17271 _17275 _17274 _17272 _17273) (@lem1045399 _17270 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1045402 (_17270 : nat) (_17271 : nat) (_17275 : nat) (_17274 : nat) (_17272 : nat) (_17273 : nat) : (term398 _17270 _17271 _17275 _17274 _17272 _17273) = (term399 _17270 _17271 _17275 _17274 _17272 _17273).
Proof. exact (MK_COMB (@lem1045401) (@lem1045400 _17270 _17271 _17275 _17274 _17272 _17273)). Qed.
Lemma lem1045403 (_17274 : nat) (_17275 : nat) : (_17274 = _17275) = (_17274 = _17275).
Proof. exact (eq_refl (_17274 = _17275)). Qed.
Lemma lem1045404 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term382 _17270 _17271 _17272 _17273 _17274 _17275) = (term400 _17270 _17271 _17272 _17273 _17274 _17275).
Proof. exact (MK_COMB (@lem1045402 _17270 _17271 _17275 _17274 _17272 _17273) (@lem1045403 _17274 _17275)). Qed.
Lemma lem1045405 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) : (term379 _17270 _17271 _17275 _17274 _17272 _17273) = (term400 _17270 _17271 _17272 _17273 _17274 _17275).
Proof. exact (TRANS (@lem1045369 _17270 _17271 _17272 _17273 _17274 _17275) (@lem1045404 _17270 _17271 _17272 _17273 _17274 _17275)). Qed.
Lemma lem1045407 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term401 z d d' x.
Proof. exact (conj (@lem1044975 d' x d z h1) (@lem1044982 d' x d z h1)). Qed.
Lemma lem1045408 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term402 z d d' x.
Proof. exact (conj (@lem1044968 z d) (@lem1045407 d' x d z h1)). Qed.
Lemma lem1045409 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term403 z d d' x.
Proof. exact (conj (@lem1044960 x d') (@lem1045408 d' x d z h1)). Qed.
Lemma lem1045411 (_17270 : nat) (_17271 : nat) (_17272 : nat) (_17273 : nat) (_17274 : nat) (_17275 : nat) (h1 : term107) : term400 _17270 _17271 _17272 _17273 _17274 _17275.
Proof. exact (EQ_MP (@lem1045405 _17270 _17271 _17272 _17273 _17274 _17275) (@lem1045366 _17270 _17271 _17275 _17274 _17272 _17273 h1)). Qed.
Lemma lem1045412 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) : term404 d' x d z.
Proof. exact (@lem1045411 d' d (Nat.add x d') x (Nat.add z d) z h1). Qed.
Lemma lem1045415 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : (Nat.add z d) = z.
Proof. exact (@lem1045412 d' x d z h1 (@lem1045409 d' x d z h2)). Qed.
Lemma lem1045416 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : term405 d z.
Proof. exact (fun h0 : term349 d z => @lem1045415 d' x d z h1 h2). Qed.
Lemma lem1045418 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045419 (d : nat) (z : nat) : (term405 d z) = ((Nat.add z d) = z).
Proof. exact (@lem1045418 ((Nat.add z d) = z)). Qed.
Lemma lem1045420 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : (Nat.add z d) = z.
Proof. exact (EQ_MP (@lem1045419 d z) (@lem1045416 d' x d z h1 h2)). Qed.
Lemma lem1045423 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1045425 (d : nat) (z : nat) : (term349 d z) = (term546 d z).
Proof. exact (@lem1045423 ((Nat.add z d) = z)). Qed.
Lemma lem1045428 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term657 d' x d z) : term546 d z.
Proof. exact (EQ_MP (@lem1045425 d z) (@lem1044748 d' x d z h1)). Qed.
Lemma lem1045431 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : False.
Proof. exact (@lem1045428 d' x d z h2 (@lem1045420 d' x d z h1 h2)). Qed.
Lemma lem1045432 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : term410.
Proof. exact (fun h0 : ~ False => @lem1045431 d' x d z h1 h2). Qed.
Lemma lem1045434 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045435 : term410 = False.
Proof. exact (@lem1045434 False). Qed.
Lemma lem1045436 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term657 d' x d z) : False.
Proof. exact (EQ_MP (@lem1045435) (@lem1045432 d' x d z h1 h2)). Qed.
Lemma lem1045470 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1045471 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1045470 (Nat.add x d')). Qed.
Lemma lem1045472 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1045471 x d'). Qed.
Lemma lem1045474 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045475 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1045474 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1045476 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1045475 x d') (@lem1045472 x d')). Qed.
Lemma lem1045478 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1045479 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1045478 (Nat.add z d)). Qed.
Lemma lem1045480 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1045479 z d). Qed.
Lemma lem1045482 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045483 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1045482 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1045484 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1045483 z d) (@lem1045480 z d)). Qed.
Lemma lem1045486 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (h1). Qed.
Lemma lem1045487 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term405 d' x.
Proof. exact (fun h0 : term349 d' x => @lem1045486 d' x h1). Qed.
Lemma lem1045489 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045490 (d' : nat) (x : nat) : (term405 d' x) = ((Nat.add x d') = x).
Proof. exact (@lem1045489 ((Nat.add x d') = x)). Qed.
Lemma lem1045491 (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : (Nat.add x d') = x.
Proof. exact (EQ_MP (@lem1045490 d' x) (@lem1045487 d' x h1)). Qed.
Lemma lem1045509 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045510 (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term415 _17281 _17285 _17284 _17282 _17283) = (term416 _17284 _17285 _17281 _17282 _17283).
Proof. exact (@lem1045509 ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284)) (term296 _17284 _17285 _17281) (term260 _17282 _17283)). Qed.
Lemma lem1045526 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045527 (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term417 _17284 _17285 _17281 _17282 _17283) = (term418 _17282 _17283 _17284 _17285 _17281).
Proof. exact (@lem1045526 (term260 _17282 _17283) (term296 _17284 _17285 _17281)). Qed.
Lemma lem1045537 (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term236 _17282 _17285 _17283 _17284) = (term236 _17282 _17285 _17283 _17284).
Proof. exact (eq_refl (term236 _17282 _17285 _17283 _17284)). Qed.
Lemma lem1045538 (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term416 _17284 _17285 _17281 _17282 _17283) = (term419 _17282 _17283 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045537 _17282 _17285 _17283 _17284) (@lem1045527 _17282 _17283 _17284 _17285 _17281)). Qed.
Lemma lem1045549 (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term415 _17281 _17285 _17284 _17282 _17283) = (term419 _17282 _17283 _17284 _17285 _17281).
Proof. exact (TRANS (@lem1045510 _17284 _17285 _17281 _17282 _17283) (@lem1045538 _17282 _17283 _17284 _17285 _17281)). Qed.
Lemma lem1045550 (_17282 : nat) (_17283 : nat) (_17280 : nat) : (term356 _17282 _17283 _17280) = (term356 _17282 _17283 _17280).
Proof. exact (eq_refl (term356 _17282 _17283 _17280)). Qed.
Lemma lem1045551 (_17280 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term420 _17280 _17282 _17283 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045550 _17282 _17283 _17280) (@lem1045549 _17282 _17283 _17284 _17285 _17281)). Qed.
Lemma lem1045555 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045556 (_17280 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term420 _17280 _17282 _17283 _17284 _17285 _17281) = (term421 _17280 _17282 _17283 _17284 _17285 _17281).
Proof. exact (@lem1045555 ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284)) (term296 _17282 _17283 _17280) (term418 _17282 _17283 _17284 _17285 _17281)). Qed.
Lemma lem1045572 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045573 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term422 _17280 _17282 _17283 _17284 _17285 _17281) = (term423 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (@lem1045572 (term260 _17282 _17283) (term296 _17282 _17283 _17280) (term296 _17284 _17285 _17281)). Qed.
Lemma lem1045595 (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term236 _17282 _17285 _17283 _17284) = (term236 _17282 _17285 _17283 _17284).
Proof. exact (eq_refl (term236 _17282 _17285 _17283 _17284)). Qed.
Lemma lem1045596 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term421 _17280 _17282 _17283 _17284 _17285 _17281) = (term424 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045595 _17282 _17285 _17283 _17284) (@lem1045573 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045607 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term420 _17280 _17282 _17283 _17284 _17285 _17281) = (term424 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (TRANS (@lem1045556 _17280 _17282 _17283 _17284 _17285 _17281) (@lem1045596 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045608 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term424 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (TRANS (@lem1045551 _17280 _17282 _17283 _17284 _17285 _17281) (@lem1045607 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1045610 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term425 _17280 _17281 _17285 _17284 _17282 _17283) = (term426 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045609) (@lem1045608 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045638 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045639 (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term417 _17284 _17285 _17281 _17282 _17283) = (term418 _17282 _17283 _17284 _17285 _17281).
Proof. exact (@lem1045638 (term260 _17282 _17283) (term296 _17284 _17285 _17281)). Qed.
Lemma lem1045649 (_17282 : nat) (_17283 : nat) (_17280 : nat) : (term356 _17282 _17283 _17280) = (term356 _17282 _17283 _17280).
Proof. exact (eq_refl (term356 _17282 _17283 _17280)). Qed.
Lemma lem1045650 (_17280 : nat) (_17282 : nat) (_17283 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term427 _17280 _17284 _17285 _17281 _17282 _17283) = (term422 _17280 _17282 _17283 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045649 _17282 _17283 _17280) (@lem1045639 _17282 _17283 _17284 _17285 _17281)). Qed.
Lemma lem1045654 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045655 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term422 _17280 _17282 _17283 _17284 _17285 _17281) = (term423 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (@lem1045654 (term260 _17282 _17283) (term296 _17282 _17283 _17280) (term296 _17284 _17285 _17281)). Qed.
Lemma lem1045677 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term427 _17280 _17284 _17285 _17281 _17282 _17283) = (term423 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (TRANS (@lem1045650 _17280 _17282 _17283 _17284 _17285 _17281) (@lem1045655 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045678 (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term236 _17282 _17285 _17283 _17284) = (term236 _17282 _17285 _17283 _17284).
Proof. exact (eq_refl (term236 _17282 _17285 _17283 _17284)). Qed.
Lemma lem1045679 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term428 _17280 _17284 _17285 _17281 _17282 _17283) = (term424 _17282 _17283 _17280 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045678 _17282 _17285 _17283 _17284) (@lem1045677 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045690 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : ((term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term428 _17280 _17284 _17285 _17281 _17282 _17283)) = ((term424 _17282 _17283 _17280 _17284 _17285 _17281) = (term424 _17282 _17283 _17280 _17284 _17285 _17281)).
Proof. exact (MK_COMB (@lem1045610 _17282 _17283 _17280 _17284 _17285 _17281) (@lem1045679 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045692 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1045693 (x : Prop) : (x = x) = True.
Proof. exact (@lem1045692 Prop x). Qed.
Lemma lem1045694 (_17282 : nat) (_17283 : nat) (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) : ((term424 _17282 _17283 _17280 _17284 _17285 _17281) = (term424 _17282 _17283 _17280 _17284 _17285 _17281)) = True.
Proof. exact (@lem1045693 (term424 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045695 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : ((term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term428 _17280 _17284 _17285 _17281 _17282 _17283)) = True.
Proof. exact (TRANS (@lem1045690 _17282 _17283 _17280 _17284 _17285 _17281) (@lem1045694 _17282 _17283 _17280 _17284 _17285 _17281)). Qed.
Lemma lem1045696 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : True = ((term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term428 _17280 _17284 _17285 _17281 _17282 _17283)).
Proof. exact (SYM (@lem1045695 _17280 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045697 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term298 _17280 _17281 _17285 _17284 _17282 _17283) = (term428 _17280 _17284 _17285 _17281 _17282 _17283).
Proof. exact (EQ_MP (@lem1045696 _17280 _17284 _17285 _17281 _17282 _17283) (@lem0)). Qed.
Lemma lem1045698 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) (h1 : term107) : term428 _17280 _17284 _17285 _17281 _17282 _17283.
Proof. exact (EQ_MP (@lem1045697 _17280 _17284 _17285 _17281 _17282 _17283) (@lem1044844 _17280 _17281 _17285 _17284 _17282 _17283 h1)). Qed.
Lemma lem1045700 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1045701 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term428 _17280 _17284 _17285 _17281 _17282 _17283) = (term429 _17280 _17281 _17282 _17285 _17283 _17284).
Proof. exact (@lem1045700 (term427 _17280 _17284 _17285 _17281 _17282 _17283) ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284))). Qed.
Lemma lem1045703 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045704 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term430 _17280 _17284 _17285 _17281 _17282 _17283) = (term431 _17280 _17284 _17285 _17281 _17282 _17283).
Proof. exact (@lem1045703 (term296 _17282 _17283 _17280) (term417 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045706 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045707 (_17282 : nat) (_17283 : nat) (_17280 : nat) : (term385 _17282 _17283 _17280) = (_17282 = (Nat.add _17283 _17280)).
Proof. exact (@lem1045706 (_17282 = (Nat.add _17283 _17280))). Qed.
Lemma lem1045708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045709 (_17282 : nat) (_17283 : nat) (_17280 : nat) : (term386 _17282 _17283 _17280) = (term387 _17282 _17283 _17280).
Proof. exact (MK_COMB (@lem1045708) (@lem1045707 _17282 _17283 _17280)). Qed.
Lemma lem1045711 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045712 (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term432 _17284 _17285 _17281 _17282 _17283) = (term433 _17284 _17285 _17281 _17282 _17283).
Proof. exact (@lem1045711 (term296 _17284 _17285 _17281) (term260 _17282 _17283)). Qed.
Lemma lem1045714 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045715 (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term385 _17284 _17285 _17281) = (_17284 = (Nat.add _17285 _17281)).
Proof. exact (@lem1045714 (_17284 = (Nat.add _17285 _17281))). Qed.
Lemma lem1045716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045717 (_17284 : nat) (_17285 : nat) (_17281 : nat) : (term386 _17284 _17285 _17281) = (term387 _17284 _17285 _17281).
Proof. exact (MK_COMB (@lem1045716) (@lem1045715 _17284 _17285 _17281)). Qed.
Lemma lem1045719 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045720 (_17282 : nat) (_17283 : nat) : (term321 _17282 _17283) = (_17282 = _17283).
Proof. exact (@lem1045719 (_17282 = _17283)). Qed.
Lemma lem1045721 (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term433 _17284 _17285 _17281 _17282 _17283) = (term434 _17284 _17285 _17281 _17282 _17283).
Proof. exact (MK_COMB (@lem1045717 _17284 _17285 _17281) (@lem1045720 _17282 _17283)). Qed.
Lemma lem1045722 (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term432 _17284 _17285 _17281 _17282 _17283) = (term434 _17284 _17285 _17281 _17282 _17283).
Proof. exact (TRANS (@lem1045712 _17284 _17285 _17281 _17282 _17283) (@lem1045721 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045723 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term431 _17280 _17284 _17285 _17281 _17282 _17283) = (term435 _17280 _17284 _17285 _17281 _17282 _17283).
Proof. exact (MK_COMB (@lem1045709 _17282 _17283 _17280) (@lem1045722 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045724 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term430 _17280 _17284 _17285 _17281 _17282 _17283) = (term435 _17280 _17284 _17285 _17281 _17282 _17283).
Proof. exact (TRANS (@lem1045704 _17280 _17284 _17285 _17281 _17282 _17283) (@lem1045723 _17280 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1045726 (_17280 : nat) (_17284 : nat) (_17285 : nat) (_17281 : nat) (_17282 : nat) (_17283 : nat) : (term436 _17280 _17284 _17285 _17281 _17282 _17283) = (term437 _17280 _17284 _17285 _17281 _17282 _17283).
Proof. exact (MK_COMB (@lem1045725) (@lem1045724 _17280 _17284 _17285 _17281 _17282 _17283)). Qed.
Lemma lem1045727 (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284)) = ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284)).
Proof. exact (eq_refl ((term53 _17282 _17284 _17283 _17285) = (term53 _17282 _17285 _17283 _17284))). Qed.
Lemma lem1045728 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term429 _17280 _17281 _17282 _17285 _17283 _17284) = (term438 _17280 _17281 _17282 _17285 _17283 _17284).
Proof. exact (MK_COMB (@lem1045726 _17280 _17284 _17285 _17281 _17282 _17283) (@lem1045727 _17282 _17285 _17283 _17284)). Qed.
Lemma lem1045729 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) : (term428 _17280 _17284 _17285 _17281 _17282 _17283) = (term438 _17280 _17281 _17282 _17285 _17283 _17284).
Proof. exact (TRANS (@lem1045701 _17280 _17281 _17282 _17285 _17283 _17284) (@lem1045728 _17280 _17281 _17282 _17285 _17283 _17284)). Qed.
Lemma lem1045731 (z : nat) (d : nat) (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term439 z d d' x.
Proof. exact (conj (@lem1045484 z d) (@lem1045491 d' x h1)). Qed.
Lemma lem1045732 (z : nat) (d : nat) (d' : nat) (x : nat) (h1 : (Nat.add x d') = x) : term440 z d d' x.
Proof. exact (conj (@lem1045476 x d') (@lem1045731 z d d' x h1)). Qed.
Lemma lem1045734 (_17280 : nat) (_17281 : nat) (_17282 : nat) (_17285 : nat) (_17283 : nat) (_17284 : nat) (h1 : term107) : term438 _17280 _17281 _17282 _17285 _17283 _17284.
Proof. exact (EQ_MP (@lem1045729 _17280 _17281 _17282 _17285 _17283 _17284) (@lem1045698 _17280 _17284 _17285 _17281 _17282 _17283 h1)). Qed.
Lemma lem1045735 (d' : nat) (x : nat) (z : nat) (d : nat) (h1 : term107) : term441 d' x z d.
Proof. exact (@lem1045734 d' d (Nat.add x d') z x (Nat.add z d) h1). Qed.
Lemma lem1045738 (z : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (@lem1045735 d' x z d h1 (@lem1045732 z d d' x h2)). Qed.
Lemma lem1045739 (z : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : term336 d' x z d.
Proof. exact (fun h0 : term337 d' x z d => @lem1045738 z d d' x h1 h2). Qed.
Lemma lem1045741 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045742 (d' : nat) (x : nat) (z : nat) (d : nat) : (term336 d' x z d) = ((term54 d' d x z) = (term58 d' x z d)).
Proof. exact (@lem1045741 ((term54 d' d x z) = (term58 d' x z d))). Qed.
Lemma lem1045743 (z : nat) (d : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : (Nat.add x d') = x) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (EQ_MP (@lem1045742 d' x z d) (@lem1045739 z d d' x h1 h2)). Qed.
Lemma lem1045746 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1045748 (d' : nat) (x : nat) (z : nat) (d : nat) : (term337 d' x z d) = (term662 d' x z d).
Proof. exact (@lem1045746 ((term54 d' d x z) = (term58 d' x z d))). Qed.
Lemma lem1045751 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term662 d' x z d.
Proof. exact (EQ_MP (@lem1045748 d' x z d) (@lem1044806 d' x d z h1)). Qed.
Lemma lem1045754 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : False.
Proof. exact (@lem1045751 d' x d z h2 (@lem1045743 z d d' x h1 h3)). Qed.
Lemma lem1045755 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : term410.
Proof. exact (fun h0 : ~ False => @lem1045754 d z d' x h1 h2 h3). Qed.
Lemma lem1045757 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045758 : term410 = False.
Proof. exact (@lem1045757 False). Qed.
Lemma lem1045759 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1045758) (@lem1045755 d z d' x h1 h2 h3)). Qed.
Lemma lem1045793 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1045794 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (@lem1045793 (Nat.add x d')). Qed.
Lemma lem1045795 (x : nat) (d' : nat) : term300 x d'.
Proof. exact (fun h0 : term301 x d' => @lem1045794 x d'). Qed.
Lemma lem1045797 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045798 (x : nat) (d' : nat) : (term300 x d') = ((Nat.add x d') = (Nat.add x d')).
Proof. exact (@lem1045797 ((Nat.add x d') = (Nat.add x d'))). Qed.
Lemma lem1045799 (x : nat) (d' : nat) : (Nat.add x d') = (Nat.add x d').
Proof. exact (EQ_MP (@lem1045798 x d') (@lem1045795 x d')). Qed.
Lemma lem1045801 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1045802 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (@lem1045801 (Nat.add z d)). Qed.
Lemma lem1045803 (z : nat) (d : nat) : term300 z d.
Proof. exact (fun h0 : term301 z d => @lem1045802 z d). Qed.
Lemma lem1045805 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045806 (z : nat) (d : nat) : (term300 z d) = ((Nat.add z d) = (Nat.add z d)).
Proof. exact (@lem1045805 ((Nat.add z d) = (Nat.add z d))). Qed.
Lemma lem1045807 (z : nat) (d : nat) : (Nat.add z d) = (Nat.add z d).
Proof. exact (EQ_MP (@lem1045806 z d) (@lem1045803 z d)). Qed.
Lemma lem1045809 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (h1). Qed.
Lemma lem1045810 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term405 d z.
Proof. exact (fun h0 : term349 d z => @lem1045809 d z h1). Qed.
Lemma lem1045812 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1045813 (d : nat) (z : nat) : (term405 d z) = ((Nat.add z d) = z).
Proof. exact (@lem1045812 ((Nat.add z d) = z)). Qed.
Lemma lem1045814 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : (Nat.add z d) = z.
Proof. exact (EQ_MP (@lem1045813 d z) (@lem1045810 d z h1)). Qed.
Lemma lem1045832 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045833 (_17292 : nat) (_17293 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term550 _17291 _17292 _17293 _17294 _17295) = (term551 _17292 _17293 _17291 _17294 _17295).
Proof. exact (@lem1045832 ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294)) (term296 _17294 _17295 _17291) (term260 _17294 _17295)). Qed.
Lemma lem1045849 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045850 (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term552 _17291 _17294 _17295) = (term553 _17294 _17295 _17291).
Proof. exact (@lem1045849 (term260 _17294 _17295) (term296 _17294 _17295 _17291)). Qed.
Lemma lem1045860 (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : (term236 _17292 _17295 _17293 _17294) = (term236 _17292 _17295 _17293 _17294).
Proof. exact (eq_refl (term236 _17292 _17295 _17293 _17294)). Qed.
Lemma lem1045861 (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term551 _17292 _17293 _17291 _17294 _17295) = (term554 _17292 _17293 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1045860 _17292 _17295 _17293 _17294) (@lem1045850 _17294 _17295 _17291)). Qed.
Lemma lem1045872 (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term550 _17291 _17292 _17293 _17294 _17295) = (term554 _17292 _17293 _17294 _17295 _17291).
Proof. exact (TRANS (@lem1045833 _17292 _17293 _17291 _17294 _17295) (@lem1045861 _17292 _17293 _17294 _17295 _17291)). Qed.
Lemma lem1045873 (_17292 : nat) (_17293 : nat) (_17290 : nat) : (term356 _17292 _17293 _17290) = (term356 _17292 _17293 _17290).
Proof. exact (eq_refl (term356 _17292 _17293 _17290)). Qed.
Lemma lem1045874 (_17290 : nat) (_17292 : nat) (_17293 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term555 _17290 _17292 _17293 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1045873 _17292 _17293 _17290) (@lem1045872 _17292 _17293 _17294 _17295 _17291)). Qed.
Lemma lem1045878 (q : Prop) (p : Prop) (r : Prop) : (term100 p q r) = (term100 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1045879 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term555 _17290 _17292 _17293 _17294 _17295 _17291) = (term556 _17292 _17293 _17290 _17294 _17295 _17291).
Proof. exact (@lem1045878 ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294)) (term296 _17292 _17293 _17290) (term553 _17294 _17295 _17291)). Qed.
Lemma lem1045913 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term556 _17292 _17293 _17290 _17294 _17295 _17291).
Proof. exact (TRANS (@lem1045874 _17290 _17292 _17293 _17294 _17295 _17291) (@lem1045879 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1045915 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term557 _17290 _17291 _17292 _17293 _17294 _17295) = (term558 _17292 _17293 _17290 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1045914) (@lem1045913 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045943 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1045944 (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term552 _17291 _17294 _17295) = (term553 _17294 _17295 _17291).
Proof. exact (@lem1045943 (term260 _17294 _17295) (term296 _17294 _17295 _17291)). Qed.
Lemma lem1045954 (_17292 : nat) (_17293 : nat) (_17290 : nat) : (term356 _17292 _17293 _17290) = (term356 _17292 _17293 _17290).
Proof. exact (eq_refl (term356 _17292 _17293 _17290)). Qed.
Lemma lem1045955 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term559 _17292 _17293 _17290 _17291 _17294 _17295) = (term560 _17292 _17293 _17290 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1045954 _17292 _17293 _17290) (@lem1045944 _17294 _17295 _17291)). Qed.
Lemma lem1045966 (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : (term236 _17292 _17295 _17293 _17294) = (term236 _17292 _17295 _17293 _17294).
Proof. exact (eq_refl (term236 _17292 _17295 _17293 _17294)). Qed.
Lemma lem1045967 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term561 _17292 _17293 _17290 _17291 _17294 _17295) = (term556 _17292 _17293 _17290 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1045966 _17292 _17295 _17293 _17294) (@lem1045955 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045978 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : ((term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term561 _17292 _17293 _17290 _17291 _17294 _17295)) = ((term556 _17292 _17293 _17290 _17294 _17295 _17291) = (term556 _17292 _17293 _17290 _17294 _17295 _17291)).
Proof. exact (MK_COMB (@lem1045915 _17292 _17293 _17290 _17294 _17295 _17291) (@lem1045967 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1045981 (x : Prop) : (x = x) = True.
Proof. exact (@lem1045980 Prop x). Qed.
Lemma lem1045982 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17294 : nat) (_17295 : nat) (_17291 : nat) : ((term556 _17292 _17293 _17290 _17294 _17295 _17291) = (term556 _17292 _17293 _17290 _17294 _17295 _17291)) = True.
Proof. exact (@lem1045981 (term556 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045983 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : ((term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term561 _17292 _17293 _17290 _17291 _17294 _17295)) = True.
Proof. exact (TRANS (@lem1045978 _17292 _17293 _17290 _17294 _17295 _17291) (@lem1045982 _17292 _17293 _17290 _17294 _17295 _17291)). Qed.
Lemma lem1045984 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : True = ((term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term561 _17292 _17293 _17290 _17291 _17294 _17295)).
Proof. exact (SYM (@lem1045983 _17292 _17293 _17290 _17291 _17294 _17295)). Qed.
Lemma lem1045985 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term538 _17290 _17291 _17292 _17293 _17294 _17295) = (term561 _17292 _17293 _17290 _17291 _17294 _17295).
Proof. exact (EQ_MP (@lem1045984 _17292 _17293 _17290 _17291 _17294 _17295) (@lem0)). Qed.
Lemma lem1045986 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) (h1 : term107) : term561 _17292 _17293 _17290 _17291 _17294 _17295.
Proof. exact (EQ_MP (@lem1045985 _17292 _17293 _17290 _17291 _17294 _17295) (@lem1044920 _17290 _17291 _17292 _17293 _17294 _17295 h1)). Qed.
Lemma lem1045988 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1045989 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : (term561 _17292 _17293 _17290 _17291 _17294 _17295) = (term562 _17290 _17291 _17292 _17295 _17293 _17294).
Proof. exact (@lem1045988 (term559 _17292 _17293 _17290 _17291 _17294 _17295) ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294))). Qed.
Lemma lem1045991 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1045992 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term563 _17292 _17293 _17290 _17291 _17294 _17295) = (term564 _17292 _17293 _17290 _17291 _17294 _17295).
Proof. exact (@lem1045991 (term296 _17292 _17293 _17290) (term552 _17291 _17294 _17295)). Qed.
Lemma lem1045994 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1045995 (_17292 : nat) (_17293 : nat) (_17290 : nat) : (term385 _17292 _17293 _17290) = (_17292 = (Nat.add _17293 _17290)).
Proof. exact (@lem1045994 (_17292 = (Nat.add _17293 _17290))). Qed.
Lemma lem1045996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1045997 (_17292 : nat) (_17293 : nat) (_17290 : nat) : (term386 _17292 _17293 _17290) = (term387 _17292 _17293 _17290).
Proof. exact (MK_COMB (@lem1045996) (@lem1045995 _17292 _17293 _17290)). Qed.
Lemma lem1045999 (a : Prop) (b : Prop) : (term316 a b) = (term317 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1046000 (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term565 _17291 _17294 _17295) = (term566 _17291 _17294 _17295).
Proof. exact (@lem1045999 (term296 _17294 _17295 _17291) (term260 _17294 _17295)). Qed.
Lemma lem1046002 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1046003 (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term385 _17294 _17295 _17291) = (_17294 = (Nat.add _17295 _17291)).
Proof. exact (@lem1046002 (_17294 = (Nat.add _17295 _17291))). Qed.
Lemma lem1046004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1046005 (_17294 : nat) (_17295 : nat) (_17291 : nat) : (term386 _17294 _17295 _17291) = (term387 _17294 _17295 _17291).
Proof. exact (MK_COMB (@lem1046004) (@lem1046003 _17294 _17295 _17291)). Qed.
Lemma lem1046007 (a : Prop) : (term320 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1046008 (_17294 : nat) (_17295 : nat) : (term321 _17294 _17295) = (_17294 = _17295).
Proof. exact (@lem1046007 (_17294 = _17295)). Qed.
Lemma lem1046009 (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term566 _17291 _17294 _17295) = (term567 _17291 _17294 _17295).
Proof. exact (MK_COMB (@lem1046005 _17294 _17295 _17291) (@lem1046008 _17294 _17295)). Qed.
Lemma lem1046010 (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term565 _17291 _17294 _17295) = (term567 _17291 _17294 _17295).
Proof. exact (TRANS (@lem1046000 _17291 _17294 _17295) (@lem1046009 _17291 _17294 _17295)). Qed.
Lemma lem1046011 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term564 _17292 _17293 _17290 _17291 _17294 _17295) = (term568 _17292 _17293 _17290 _17291 _17294 _17295).
Proof. exact (MK_COMB (@lem1045997 _17292 _17293 _17290) (@lem1046010 _17291 _17294 _17295)). Qed.
Lemma lem1046012 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term563 _17292 _17293 _17290 _17291 _17294 _17295) = (term568 _17292 _17293 _17290 _17291 _17294 _17295).
Proof. exact (TRANS (@lem1045992 _17292 _17293 _17290 _17291 _17294 _17295) (@lem1046011 _17292 _17293 _17290 _17291 _17294 _17295)). Qed.
Lemma lem1046013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1046014 (_17292 : nat) (_17293 : nat) (_17290 : nat) (_17291 : nat) (_17294 : nat) (_17295 : nat) : (term569 _17292 _17293 _17290 _17291 _17294 _17295) = (term570 _17292 _17293 _17290 _17291 _17294 _17295).
Proof. exact (MK_COMB (@lem1046013) (@lem1046012 _17292 _17293 _17290 _17291 _17294 _17295)). Qed.
Lemma lem1046015 (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294)) = ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294)).
Proof. exact (eq_refl ((term53 _17292 _17294 _17293 _17295) = (term53 _17292 _17295 _17293 _17294))). Qed.
Lemma lem1046016 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : (term562 _17290 _17291 _17292 _17295 _17293 _17294) = (term571 _17290 _17291 _17292 _17295 _17293 _17294).
Proof. exact (MK_COMB (@lem1046014 _17292 _17293 _17290 _17291 _17294 _17295) (@lem1046015 _17292 _17295 _17293 _17294)). Qed.
Lemma lem1046017 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) : (term561 _17292 _17293 _17290 _17291 _17294 _17295) = (term571 _17290 _17291 _17292 _17295 _17293 _17294).
Proof. exact (TRANS (@lem1045989 _17290 _17291 _17292 _17295 _17293 _17294) (@lem1046016 _17290 _17291 _17292 _17295 _17293 _17294)). Qed.
Lemma lem1046019 (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term572 d z.
Proof. exact (conj (@lem1045807 z d) (@lem1045814 d z h1)). Qed.
Lemma lem1046020 (x : nat) (d' : nat) (d : nat) (z : nat) (h1 : (Nat.add z d) = z) : term573 x d' d z.
Proof. exact (conj (@lem1045799 x d') (@lem1046019 d z h1)). Qed.
Lemma lem1046022 (_17290 : nat) (_17291 : nat) (_17292 : nat) (_17295 : nat) (_17293 : nat) (_17294 : nat) (h1 : term107) : term571 _17290 _17291 _17292 _17295 _17293 _17294.
Proof. exact (EQ_MP (@lem1046017 _17290 _17291 _17292 _17295 _17293 _17294) (@lem1045986 _17292 _17293 _17290 _17291 _17294 _17295 h1)). Qed.
Lemma lem1046023 (d' : nat) (x : nat) (z : nat) (d : nat) (h1 : term107) : term574 d' x z d.
Proof. exact (@lem1046022 d' d (Nat.add x d') z x (Nat.add z d) h1). Qed.
Lemma lem1046026 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (@lem1046023 d' x z d h1 (@lem1046020 x d' d z h2)). Qed.
Lemma lem1046027 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : term336 d' x z d.
Proof. exact (fun h0 : term337 d' x z d => @lem1046026 d' x d z h1 h2). Qed.
Lemma lem1046029 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1046030 (d' : nat) (x : nat) (z : nat) (d : nat) : (term336 d' x z d) = ((term54 d' d x z) = (term58 d' x z d)).
Proof. exact (@lem1046029 ((term54 d' d x z) = (term58 d' x z d))). Qed.
Lemma lem1046031 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : (Nat.add z d) = z) : (term54 d' d x z) = (term58 d' x z d).
Proof. exact (EQ_MP (@lem1046030 d' x z d) (@lem1046027 d' x d z h1 h2)). Qed.
Lemma lem1046034 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1046036 (d' : nat) (x : nat) (z : nat) (d : nat) : (term337 d' x z d) = (term662 d' x z d).
Proof. exact (@lem1046034 ((term54 d' d x z) = (term58 d' x z d))). Qed.
Lemma lem1046039 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term654 d' x d z) : term662 d' x z d.
Proof. exact (EQ_MP (@lem1046036 d' x z d) (@lem1044866 d' x d z h1)). Qed.
Lemma lem1046042 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : False.
Proof. exact (@lem1046039 d' x d z h2 (@lem1046031 d' x d z h1 h3)). Qed.
Lemma lem1046043 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : term410.
Proof. exact (fun h0 : ~ False => @lem1046042 d' x d z h1 h2 h3). Qed.
Lemma lem1046045 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1046046 : term410 = False.
Proof. exact (@lem1046045 False). Qed.
Lemma lem1046047 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1046046) (@lem1046043 d' x d z h1 h2 h3)). Qed.
Lemma lem1046048 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add z d) = z => @lem1046047 d' x d z h1 h2 h3) (fun h4 : False => @lem1044868 d z h3)). Qed.
Lemma lem1046049 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1046048 d' x d z h1 h2 h3) (@lem1044868 d z h3)). Qed.
Lemma lem1046050 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1045759 d z d' x h1 h2 h3) (fun h4 : False => @lem1044808 d' x h3)). Qed.
Lemma lem1046051 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1046050 d z d' x h1 h2 h3) (@lem1044808 d' x h3)). Qed.
Lemma lem1046052 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add z d) = z => @lem1046049 d' x d z h1 h2 h3) (fun h4 : False => @lem1044636 d z h3)). Qed.
Lemma lem1046053 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1046052 d' x d z h1 h2 h3) (@lem1044636 d z h3)). Qed.
Lemma lem1046054 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1046051 d z d' x h1 h2 h3) (fun h4 : False => @lem1044530 d' x h3)). Qed.
Lemma lem1046055 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1046054 d z d' x h1 h2 h3) (@lem1044530 d' x h3)). Qed.
Lemma lem1046056 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : ((Nat.add z d) = z) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add z d) = z => @lem1046053 d' x d z h1 h2 h3) (fun h4 : False => @lem1044636 d z h3)). Qed.
Lemma lem1046057 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add z d) = z) : False.
Proof. exact (EQ_MP (@lem1046056 d' x d z h1 h2 h3) (@lem1044636 d z h3)). Qed.
Lemma lem1046058 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : ((Nat.add x d') = x) = False.
Proof. exact (prop_ext (fun h4 : (Nat.add x d') = x => @lem1046055 d z d' x h1 h2 h3) (fun h4 : False => @lem1044530 d' x h3)). Qed.
Lemma lem1046059 (d : nat) (z : nat) (d' : nat) (x : nat) (h1 : term107) (h2 : term654 d' x d z) (h3 : (Nat.add x d') = x) : False.
Proof. exact (EQ_MP (@lem1046058 d z d' x h1 h2 h3) (@lem1044530 d' x h3)). Qed.
Lemma lem1046060 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term654 d' x d z) : False.
Proof. exact (or_elim (@lem1044311 d' x d z h2) (fun h0 : (Nat.add x d') = x => @lem1046059 d z d' x h1 h2 h0) (fun h0 : (Nat.add z d) = z => @lem1046057 d' x d z h1 h2 h0)). Qed.
Lemma lem1046061 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term107) (h2 : term629 d' x d z) : False.
Proof. exact (or_elim (@lem1044118 d' x d z h2) (fun h0 : term657 d' x d z => @lem1045436 d' x d z h1 h0) (fun h0 : term654 d' x d z => @lem1046060 d' x d z h1 h0)). Qed.
Lemma lem1046062 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term181.
Proof. exact (fun h0 : term107 => @lem1046061 d' x d z h0 h1). Qed.
Lemma lem1046063 : term181 = term182.
Proof. exact (@lem69 term107). Qed.
Lemma lem1046064 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term182.
Proof. exact (EQ_MP (@lem1046063) (@lem1046062 d' x d z h1)). Qed.
Lemma lem1046065 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term185.
Proof. exact (fun h0 : term216 => @lem1046064 d' x d z h1). Qed.
Lemma lem1046066 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term188.
Proof. exact (fun h0 : term220 => @lem1046065 d' x d z h1). Qed.
Lemma lem1046067 (d' : nat) (x : nat) (d : nat) (z : nat) : term635 d' x d z.
Proof. exact (fun h0 : term629 d' x d z => @lem1046066 d' x d z h0). Qed.
Lemma lem1046072 (x : nat) (d : nat) (z : nat) : term639 x d z.
Proof. exact (fun d' : nat => @lem1046067 d' x d z). Qed.
Lemma lem1046077 (d : nat) (z : nat) : term643 d z.
Proof. exact (fun x : nat => @lem1046072 x d z). Qed.
Lemma lem1046082 (z : nat) : term647 z.
Proof. exact (fun d : nat => @lem1046077 d z). Qed.
Lemma lem1046087 : term651.
Proof. exact (fun z : nat => @lem1046082 z). Qed.
Lemma lem1046088 : term650.
Proof. exact (EQ_MP (@lem1043768) (@lem1046087)). Qed.
Lemma lem1046089 (z : nat) : term663 z.
Proof. exact (@lem1046088 z). Qed.
Lemma lem1046090 (z : nat) : (term663 z) = (term646 z).
Proof. exact (eq_refl (term663 z)). Qed.
Lemma lem1046091 (z : nat) : term646 z.
Proof. exact (EQ_MP (@lem1046090 z) (@lem1046089 z)). Qed.
Lemma lem1046092 (z : nat) (d : nat) : term664 z d.
Proof. exact (@lem1046091 z d). Qed.
Lemma lem1046093 (d : nat) (z : nat) : (term664 z d) = (term642 d z).
Proof. exact (eq_refl (term664 z d)). Qed.
Lemma lem1046094 (d : nat) (z : nat) : term642 d z.
Proof. exact (EQ_MP (@lem1046093 d z) (@lem1046092 z d)). Qed.
Lemma lem1046095 (d : nat) (z : nat) (x : nat) : term665 d z x.
Proof. exact (@lem1046094 d z x). Qed.
Lemma lem1046096 (x : nat) (d : nat) (z : nat) : (term665 d z x) = (term638 x d z).
Proof. exact (eq_refl (term665 d z x)). Qed.
Lemma lem1046097 (x : nat) (d : nat) (z : nat) : term638 x d z.
Proof. exact (EQ_MP (@lem1046096 x d z) (@lem1046095 d z x)). Qed.
Lemma lem1046098 (x : nat) (d : nat) (z : nat) (d' : nat) : term666 x d z d'.
Proof. exact (@lem1046097 x d z d'). Qed.
Lemma lem1046099 (d' : nat) (x : nat) (d : nat) (z : nat) : (term666 x d z d') = (term630 d' x d z).
Proof. exact (eq_refl (term666 x d z d')). Qed.
Lemma lem1046100 (d' : nat) (x : nat) (d : nat) (z : nat) : term630 d' x d z.
Proof. exact (EQ_MP (@lem1046099 d' x d z) (@lem1046098 x d z d')). Qed.
Lemma lem1046102 (d' : nat) (x : nat) (d : nat) (z : nat) : term630 d' x d z.
Proof. exact (@lem1043466 d' x d z (@lem1046100 d' x d z)). Qed.
Lemma lem1046103 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term187.
Proof. exact (@lem1046102 d' x d z (@lem1043451 d' x d z h1)). Qed.
Lemma lem1046104 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term184.
Proof. exact (@lem1046103 d' x d z h1 (@lem81820)). Qed.
Lemma lem1046105 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : term181.
Proof. exact (@lem1046104 d' x d z h1 (@lem77775)). Qed.
Lemma lem1046106 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : False.
Proof. exact (@lem1046105 d' x d z h1 (@lem1033477)). Qed.
Lemma lem1046107 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : (term629 d' x d z) = False.
Proof. exact (prop_ext (fun h2 : term629 d' x d z => @lem1046106 d' x d z h1) (fun h2 : False => @lem1043451 d' x d z h1)). Qed.
Lemma lem1046108 (d' : nat) (x : nat) (d : nat) (z : nat) (h1 : term629 d' x d z) : False.
Proof. exact (EQ_MP (@lem1046107 d' x d z h1) (@lem1043451 d' x d z h1)). Qed.
Lemma lem1046109 (d' : nat) (x : nat) (d : nat) (z : nat) : term628 d' x d z.
Proof. exact (fun h0 : term629 d' x d z => @lem1046108 d' x d z h0). Qed.
Lemma lem1046110 (d' : nat) (x : nat) (d : nat) (z : nat) : ((term54 d' d x z) = (term58 d' x z d)) = (term65 d' x d z).
Proof. exact (EQ_MP (@lem1043450 d' x d z) (@lem1046109 d' x d z)). Qed.
Lemma lem1046111 (d : nat) (z : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : ((term142 w d x z) = (term141 w x z d)) = (term157 w x d z).
Proof. exact (EQ_MP (@lem1033918 d z w x d' h1) (@lem1046110 d' x d z)). Qed.
Lemma lem1046112 (d : nat) (z : nat) (x : nat) (w : nat) (h1 : Peano.le x w) : ((term142 w d x z) = (term141 w x z d)) = (term157 w x d z).
Proof. exact (ex_elim (@lem1033904 x w h1) (fun d' : nat => fun h0 : term667 w x d' => @lem1046111 d z w x d' h0)). Qed.
Lemma lem1046113 (x : nat) (w : nat) (y : nat) (z : nat) (d : nat) (h1 : Peano.le x w) (h2 : y = (Nat.add z d)) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (EQ_MP (@lem1033894 w x y z d h2) (@lem1046112 d z x w h1)). Qed.
Lemma lem1046114 (x : nat) (w : nat) (z : nat) (y : nat) (h1 : Peano.le x w) (h2 : Peano.le z y) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (ex_elim (@lem1033880 z y h2) (fun d : nat => fun h0 : term667 y z d => @lem1046113 x w y z d h1 h0)). Qed.
Lemma lem1046115 (y : nat) (d : nat) (w : nat) (x : nat) (d' : nat) (h1 : w = (Nat.add x d')) : ((term141 w x y d) = (term142 w d x y)) = (term143 w x y d).
Proof. exact (EQ_MP (@lem1033870 y d w x d' h1) (@lem1043446 d' x y d)). Qed.
Lemma lem1046116 (y : nat) (d : nat) (x : nat) (w : nat) (h1 : Peano.le x w) : ((term141 w x y d) = (term142 w d x y)) = (term143 w x y d).
Proof. exact (ex_elim (@lem1033856 x w h1) (fun d' : nat => fun h0 : term667 w x d' => @lem1046115 y d w x d' h0)). Qed.
Lemma lem1046117 (x : nat) (w : nat) (z : nat) (y : nat) (d : nat) (h1 : Peano.le x w) (h2 : z = (Nat.add y d)) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (EQ_MP (@lem1033846 w x z y d h2) (@lem1046116 y d x w h1)). Qed.
Lemma lem1046118 (x : nat) (w : nat) (y : nat) (z : nat) (h1 : Peano.le x w) (h2 : Peano.le y z) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (ex_elim (@lem1033832 y z h2) (fun d : nat => fun h0 : term667 z y d => @lem1046117 x w z y d h1 h0)). Qed.
Lemma lem1046119 (d : nat) (z : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : ((term142 w d x z) = (term141 w x z d)) = (term157 w x d z).
Proof. exact (EQ_MP (@lem1033822 d z x w d' h1) (@lem1040346 w d' d z)). Qed.
Lemma lem1046120 (d : nat) (z : nat) (w : nat) (x : nat) (h1 : Peano.le w x) : ((term142 w d x z) = (term141 w x z d)) = (term157 w x d z).
Proof. exact (ex_elim (@lem1033808 w x h1) (fun d' : nat => fun h0 : term667 x w d' => @lem1046119 d z x w d' h0)). Qed.
Lemma lem1046121 (w : nat) (x : nat) (y : nat) (z : nat) (d : nat) (h1 : Peano.le w x) (h2 : y = (Nat.add z d)) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (EQ_MP (@lem1033798 w x y z d h2) (@lem1046120 d z w x h1)). Qed.
Lemma lem1046122 (w : nat) (x : nat) (z : nat) (y : nat) (h1 : Peano.le w x) (h2 : Peano.le z y) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (ex_elim (@lem1033784 z y h2) (fun d : nat => fun h0 : term667 y z d => @lem1046121 w x y z d h1 h0)). Qed.
Lemma lem1046123 (y : nat) (d : nat) (x : nat) (w : nat) (d' : nat) (h1 : x = (Nat.add w d')) : ((term141 w x y d) = (term142 w d x y)) = (term143 w x y d).
Proof. exact (EQ_MP (@lem1033774 y d x w d' h1) (@lem1037156 w d' y d)). Qed.
Lemma lem1046124 (y : nat) (d : nat) (w : nat) (x : nat) (h1 : Peano.le w x) : ((term141 w x y d) = (term142 w d x y)) = (term143 w x y d).
Proof. exact (ex_elim (@lem1033760 w x h1) (fun d' : nat => fun h0 : term667 x w d' => @lem1046123 y d x w d' h0)). Qed.
Lemma lem1046125 (w : nat) (x : nat) (z : nat) (y : nat) (d : nat) (h1 : Peano.le w x) (h2 : z = (Nat.add y d)) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (EQ_MP (@lem1033750 w x z y d h2) (@lem1046124 y d w x h1)). Qed.
Lemma lem1046126 (w : nat) (x : nat) (y : nat) (z : nat) (h1 : Peano.le w x) (h2 : Peano.le y z) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (ex_elim (@lem1033736 y z h2) (fun d : nat => fun h0 : term667 z y d => @lem1046125 w x z y d h1 h0)). Qed.
Lemma lem1046127 (y : nat) (z : nat) (x : nat) (w : nat) (h1 : Peano.le x w) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (or_elim (@lem1033489 z y) (fun h0 : Peano.le y z => @lem1046118 x w y z h1 h0) (fun h0 : Peano.le z y => @lem1046114 x w z y h1 h0)). Qed.
Lemma lem1046128 (y : nat) (z : nat) (w : nat) (x : nat) (h1 : Peano.le w x) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (or_elim (@lem1033489 z y) (fun h0 : Peano.le y z => @lem1046126 w x y z h1 h0) (fun h0 : Peano.le z y => @lem1046122 w x z y h1 h0)). Qed.
Lemma lem1046129 (w : nat) (x : nat) (y : nat) (z : nat) : ((term53 w y x z) = (term53 w z x y)) = (term64 w x y z).
Proof. exact (or_elim (@lem1033497 x w) (fun h0 : Peano.le w x => @lem1046128 y z w x h0) (fun h0 : Peano.le x w => @lem1046127 y z x w h0)). Qed.
Lemma lem1046134 (w : nat) (x : nat) (y : nat) : term668 w x y.
Proof. exact (fun z : nat => @lem1046129 w x y z). Qed.
Lemma lem1046139 (w : nat) (x : nat) : term669 w x.
Proof. exact (fun y : nat => @lem1046134 w x y). Qed.
Lemma lem1046144 (w : nat) : term670 w.
Proof. exact (fun x : nat => @lem1046139 w x). Qed.
Lemma lem1046149 : term134.
Proof. exact (fun w : nat => @lem1046144 w). Qed.
Lemma lem1046150 : term137.
Proof. exact (EQ_MP (@lem1033726) (@lem1046149)). Qed.
Lemma lem1046211 {A : Type'} (add : type1400 A) : term671 A add.
Proof. exact (@lem1032609 A add). Qed.
Lemma lem1046212 {A : Type'} (add : type1400 A) : (term671 A add) = (term672 A add).
Proof. exact (eq_refl (term671 A add)). Qed.
Lemma lem1046213 {A : Type'} (add : type1400 A) : term672 A add.
Proof. exact (EQ_MP (@lem1046212 A add) (@lem1046211 A add)). Qed.
Lemma lem1046214 {A : Type'} (add : type1400 A) (mul : type1400 A) : term673 A add mul.
Proof. exact (@lem1046213 A add mul). Qed.
Lemma lem1046215 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term673 A add mul) = (term674 A add mul).
Proof. exact (eq_refl (term673 A add mul)). Qed.
Lemma lem1046216 {A : Type'} (add : type1400 A) (mul : type1400 A) : term674 A add mul.
Proof. exact (EQ_MP (@lem1046215 A add mul) (@lem1046214 A add mul)). Qed.
Lemma lem1046217 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) : term675 A add mul n0.
Proof. exact (@lem1046216 A add mul n0). Qed.
Lemma lem1046218 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : (term675 A add mul n0) = (term676 A n0 add mul).
Proof. exact (eq_refl (term675 A add mul n0)). Qed.
Lemma lem1046221 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : term676 A n0 add mul.
Proof. exact (EQ_MP (@lem1046218 A n0 add mul) (@lem1046217 A add mul n0)). Qed.
Lemma lem1046222 (n0 : nat) (add : type1606) (mul : type1606) : term677 n0 add mul.
Proof. exact (@lem1046221 nat n0 add mul). Qed.
Lemma lem1046223 : term678.
Proof. exact (@lem1046222 (NUMERAL 0) Nat.add Nat.mul). Qed.
Lemma lem1046224 : term679.
Proof. exact (@lem1046223 (@lem1046150)). Qed.
