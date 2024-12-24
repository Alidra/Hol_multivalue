Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1251285_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1251043 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251044 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 n d' d'' d''') = (term3 n d' d'' d''').
Proof. exact (@lem1251043 n d' (term4 d' d'' d''')). Qed.
Lemma lem1251046 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251047 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 n d' d'' d''') = (term5 n d' d'' d''').
Proof. exact (@lem1251046 d' n (term4 d' d'' d''')). Qed.
Lemma lem1251054 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 n d' d'' d''') = (term5 n d' d'' d''').
Proof. exact (TRANS (@lem1251044 n d' d'' d''') (@lem1251047 n d' d'' d''')). Qed.
Lemma lem1251062 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251063 (d' : nat) (d'' : nat) (d''' : nat) : (term4 d' d'' d''') = (term6 d' d'' d''').
Proof. exact (@lem1251062 d' d'' (S d''')). Qed.
Lemma lem1251073 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1251074 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term8 n d' d'' d''').
Proof. exact (MK_COMB (@lem1251073 n) (@lem1251063 d' d'' d''')). Qed.
Lemma lem1251076 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251077 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term8 n d' d'' d''') = (term8 d' n d'' d''').
Proof. exact (@lem1251076 d' n (term9 d'' d''')). Qed.
Lemma lem1251085 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251086 (d'' : nat) (n : nat) (d''' : nat) : (term6 n d'' d''') = (term6 d'' n d''').
Proof. exact (@lem1251085 d'' n (S d''')). Qed.
Lemma lem1251096 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251097 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 d' n d'' d''') = (term8 d' d'' n d''').
Proof. exact (MK_COMB (@lem1251096 d') (@lem1251086 d'' n d''')). Qed.
Lemma lem1251104 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 n d' d'' d''') = (term8 d' d'' n d''').
Proof. exact (TRANS (@lem1251077 d' n d'' d''') (@lem1251097 d' d'' n d''')). Qed.
Lemma lem1251105 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 n d' d'' d''') = (term8 d' d'' n d''').
Proof. exact (TRANS (@lem1251074 n d' d'' d''') (@lem1251104 d' d'' n d''')). Qed.
Lemma lem1251106 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251107 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 n d' d'' d''') = (term10 d' d'' n d''').
Proof. exact (MK_COMB (@lem1251106 d') (@lem1251105 d' d'' n d''')). Qed.
Lemma lem1251114 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term2 n d' d'' d''') = (term10 d' d'' n d''').
Proof. exact (TRANS (@lem1251054 n d' d'' d''') (@lem1251107 d' d'' n d''')). Qed.
Lemma lem1251115 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251116 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 n d' d'' d''') = (term12 d' d'' n d''').
Proof. exact (MK_COMB (@lem1251115) (@lem1251114 d' d'' n d''')). Qed.
Lemma lem1251118 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251119 (d'' : nat) (n : nat) (d''' : nat) (d' : nat) : (term13 n d'' d''' d') = (term13 d'' n d''' d').
Proof. exact (@lem1251118 d'' n (term14 d''' d')). Qed.
Lemma lem1251133 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251134 (d''' : nat) (d' : nat) : (term14 d''' d') = (term15 d''' d').
Proof. exact (@lem1251133 d' (S d''') d'). Qed.
Lemma lem1251142 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251143 (d' : nat) (d''' : nat) : (term16 d''' d') = (term9 d' d''').
Proof. exact (@lem1251142 d' (S d''')). Qed.
Lemma lem1251147 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251148 (d' : nat) (d''' : nat) : (term15 d''' d') = (term17 d' d''').
Proof. exact (MK_COMB (@lem1251147 d') (@lem1251143 d' d''')). Qed.
Lemma lem1251155 (d' : nat) (d''' : nat) : (term14 d''' d') = (term17 d' d''').
Proof. exact (TRANS (@lem1251134 d''' d') (@lem1251148 d' d''')). Qed.
Lemma lem1251156 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1251157 (n : nat) (d' : nat) (d''' : nat) : (term18 n d''' d') = (term19 n d' d''').
Proof. exact (MK_COMB (@lem1251156 n) (@lem1251155 d' d''')). Qed.
Lemma lem1251159 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251160 (n : nat) (d' : nat) (d''' : nat) : (term19 n d' d''') = (term20 n d' d''').
Proof. exact (@lem1251159 d' n (term9 d' d''')). Qed.
Lemma lem1251168 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251169 (d' : nat) (n : nat) (d''' : nat) : (term6 n d' d''') = (term6 d' n d''').
Proof. exact (@lem1251168 d' n (S d''')). Qed.
Lemma lem1251179 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251180 (d' : nat) (n : nat) (d''' : nat) : (term20 n d' d''') = (term21 d' n d''').
Proof. exact (MK_COMB (@lem1251179 d') (@lem1251169 d' n d''')). Qed.
Lemma lem1251187 (d' : nat) (n : nat) (d''' : nat) : (term19 n d' d''') = (term21 d' n d''').
Proof. exact (TRANS (@lem1251160 n d' d''') (@lem1251180 d' n d''')). Qed.
Lemma lem1251188 (d' : nat) (n : nat) (d''' : nat) : (term18 n d''' d') = (term21 d' n d''').
Proof. exact (TRANS (@lem1251157 n d' d''') (@lem1251187 d' n d''')). Qed.
Lemma lem1251189 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251190 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term13 d'' n d''' d') = (term22 d'' d' n d''').
Proof. exact (MK_COMB (@lem1251189 d'') (@lem1251188 d' n d''')). Qed.
Lemma lem1251192 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251193 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term22 d'' d' n d''') = (term23 d'' d' n d''').
Proof. exact (@lem1251192 d' d'' (term6 d' n d''')). Qed.
Lemma lem1251201 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251202 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 d'' d' n d''') = (term8 d' d'' n d''').
Proof. exact (@lem1251201 d' d'' (term9 n d''')). Qed.
Lemma lem1251218 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251219 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term23 d'' d' n d''') = (term10 d' d'' n d''').
Proof. exact (MK_COMB (@lem1251218 d') (@lem1251202 d' d'' n d''')). Qed.
Lemma lem1251226 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term22 d'' d' n d''') = (term10 d' d'' n d''').
Proof. exact (TRANS (@lem1251193 d'' d' n d''') (@lem1251219 d' d'' n d''')). Qed.
Lemma lem1251227 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 d'' n d''' d') = (term10 d' d'' n d''').
Proof. exact (TRANS (@lem1251190 d'' d' n d''') (@lem1251226 d' d'' n d''')). Qed.
Lemma lem1251228 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 n d'' d''' d') = (term10 d' d'' n d''').
Proof. exact (TRANS (@lem1251119 d'' n d''' d') (@lem1251227 d' d'' n d''')). Qed.
Lemma lem1251229 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term2 n d' d'' d''') = (term13 n d'' d''' d')) = ((term10 d' d'' n d''') = (term10 d' d'' n d''')).
Proof. exact (MK_COMB (@lem1251116 d' d'' n d''') (@lem1251228 d' d'' n d''')). Qed.
Lemma lem1251231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251232 (x : nat) : (x = x) = True.
Proof. exact (@lem1251231 nat x). Qed.
Lemma lem1251233 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term10 d' d'' n d''') = (term10 d' d'' n d''')) = True.
Proof. exact (@lem1251232 (term10 d' d'' n d''')). Qed.
Lemma lem1251234 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term2 n d' d'' d''') = (term13 n d'' d''' d')) = True.
Proof. exact (TRANS (@lem1251229 d' d'' n d''') (@lem1251233 d' d'' n d''')). Qed.
Lemma lem1251235 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : True = ((term2 n d' d'' d''') = (term13 n d'' d''' d')).
Proof. exact (SYM (@lem1251234 n d'' d''' d')). Qed.
Lemma lem1251236 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term2 n d' d'' d''') = (term13 n d'' d''' d').
Proof. exact (EQ_MP (@lem1251235 n d'' d''' d') (@lem0)). Qed.
Lemma lem1251238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251239 (x : nat) : (x = x) = True.
Proof. exact (@lem1251238 nat x). Qed.
Lemma lem1251240 (n : nat) (d'' : nat) : ((Nat.add n d'') = (Nat.add n d'')) = True.
Proof. exact (@lem1251239 (Nat.add n d'')). Qed.
Lemma lem1251241 (n : nat) (d'' : nat) : True = ((Nat.add n d'') = (Nat.add n d'')).
Proof. exact (SYM (@lem1251240 n d'')). Qed.
Lemma lem1251242 (n : nat) (d'' : nat) : (Nat.add n d'') = (Nat.add n d'').
Proof. exact (EQ_MP (@lem1251241 n d'') (@lem0)). Qed.
Lemma lem1251243 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251244 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term11 n d' d'' d''') = (term24 n d'' d''' d').
Proof. exact (MK_COMB (@lem1251243) (@lem1251236 n d'' d''' d')). Qed.
Lemma lem1251245 (d''' : nat) (d' : nat) (n : nat) (d'' : nat) : ((term2 n d' d'' d''') = (Nat.add n d'')) = ((term13 n d'' d''' d') = (Nat.add n d'')).
Proof. exact (MK_COMB (@lem1251244 n d'' d''' d') (@lem1251242 n d'')). Qed.
Lemma lem1251252 (m : nat) : term25 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1251253 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1251254 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1251253 m) (@lem1251252 m)). Qed.
Lemma lem1251255 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem1251254 m n). Qed.
Lemma lem1251256 (m : nat) (n : nat) : (term27 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1251258 (m : nat) : term28 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1251259 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1251260 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1251259 m) (@lem1251258 m)). Qed.
Lemma lem1251261 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1251260 m n). Qed.
Lemma lem1251262 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1251263 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem1251262 m n) (@lem1251261 m n)). Qed.
Lemma lem1251264 (m : nat) (n : nat) (p : nat) : term32 m n p.
Proof. exact (@lem1251263 m n p). Qed.
Lemma lem1251265 (m : nat) (n : nat) (p : nat) : (term32 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term32 m n p)). Qed.
Lemma lem1251268 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1251265 m n p) (@lem1251264 m n p)). Qed.
Lemma lem1251269 (n : nat) (d''' : nat) (d' : nat) (d'' : nat) : ((term13 n d'' d''' d') = (Nat.add n d'')) = ((term18 d'' d''' d') = d'').
Proof. exact (@lem1251268 n (term18 d'' d''' d') d''). Qed.
Lemma lem1251271 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251256 m n) (@lem1251255 m n)). Qed.
Lemma lem1251276 (d'' : nat) (d''' : nat) (d' : nat) : ((term18 d'' d''' d') = d'') = ((term14 d''' d') = (NUMERAL 0)).
Proof. exact (@lem1251271 d'' (term14 d''' d')). Qed.
Lemma lem1251277 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term13 n d'' d''' d') = (Nat.add n d'')) = ((term14 d''' d') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1251269 n d''' d' d'') (@lem1251276 d'' d''' d')). Qed.
Lemma lem1251278 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term33 d' d''' n d'') = (term33 d' d''' n d'').
Proof. exact (eq_refl (term33 d' d''' n d'')). Qed.
Lemma lem1251279 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : (((term2 n d' d'' d''') = (Nat.add n d'')) = ((term13 n d'' d''' d') = (Nat.add n d''))) = (((term2 n d' d'' d''') = (Nat.add n d'')) = ((term14 d''' d') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1251278 d' d''' n d'') (@lem1251277 n d'' d''' d')). Qed.
Lemma lem1251280 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term2 n d' d'' d''') = (Nat.add n d'')) = ((term14 d''' d') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251279 n d'' d''' d') (@lem1251245 d''' d' n d'')). Qed.
Lemma lem1251281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1251282 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term34 d' d''' n d'') = (term35 d''' d').
Proof. exact (MK_COMB (@lem1251281) (@lem1251280 n d'' d''' d')). Qed.
Lemma lem1251283 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1251284 (n : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term36 d' d''' n d'') = (term37 d''' d').
Proof. exact (MK_COMB (@lem1251282 n d'' d''' d') (@lem1251283)). Qed.
Lemma lem1251285 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term37 d''' d') = (term36 d' d''' n d'').
Proof. exact (SYM (@lem1251284 n d'' d''' d')). Qed.
