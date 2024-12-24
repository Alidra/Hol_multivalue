Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_PSUBSET_IMP_term_abbrevs.
Require Import PSUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3921108 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3195125 A s). Qed.
Lemma lem3921109 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3921110 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3921109 A s) (@lem3921108 A s)). Qed.
Lemma lem3921111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3921110 A s t). Qed.
Lemma lem3921112 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@PSUBSET A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3921129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3921112 A s t) (@lem3921111 A s t)). Qed.
Lemma lem3921130 {_100951 : Type'} (s : _100951 -> Prop) (t : _100951 -> Prop) : (@PSUBSET _100951 s t) = (term3 _100951 s t).
Proof. exact (@lem3921129 _100951 s t). Qed.
Lemma lem3921131 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (@PSUBSET _100951 a b) = (term3 _100951 a b).
Proof. exact (@lem3921130 _100951 a b). Qed.
Lemma lem3921136 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term4 _100951 a b) = (term4 _100951 a b).
Proof. exact (eq_refl (term4 _100951 a b)). Qed.
Lemma lem3921137 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term5 _100951 a b) = (term6 _100951 a b).
Proof. exact (MK_COMB (@lem3921136 _100951 a b) (@lem3921131 _100951 a b)). Qed.
Lemma lem3921140 {_100951 : Type'} (a : _100951 -> Prop) : (term7 _100951 a) = (term8 _100951 a).
Proof. exact (fun_ext (fun b : _100951 -> Prop => @lem3921137 _100951 a b)). Qed.
Lemma lem3921141 {_100951 : Type'} : (@all (_100951 -> Prop)) = (@all (_100951 -> Prop)).
Proof. exact (eq_refl (@all (_100951 -> Prop))). Qed.
Lemma lem3921142 {_100951 : Type'} (a : _100951 -> Prop) : (term9 _100951 a) = (term10 _100951 a).
Proof. exact (MK_COMB (@lem3921141 _100951) (@lem3921140 _100951 a)). Qed.
Lemma lem3921147 {_100951 : Type'} : (term11 _100951) = (term12 _100951).
Proof. exact (fun_ext (fun a : _100951 -> Prop => @lem3921142 _100951 a)). Qed.
Lemma lem3921148 {_100951 : Type'} : (@all (_100951 -> Prop)) = (@all (_100951 -> Prop)).
Proof. exact (eq_refl (@all (_100951 -> Prop))). Qed.
Lemma lem3921149 {_100951 : Type'} : (term13 _100951) = (term14 _100951).
Proof. exact (MK_COMB (@lem3921148 _100951) (@lem3921147 _100951)). Qed.
Lemma lem3921154 {_100951 : Type'} : (term14 _100951) = (term13 _100951).
Proof. exact (SYM (@lem3921149 _100951)). Qed.
Lemma lem3921156 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3921157 {_100951 : Type'} : (term14 _100951) = (term16 _100951).
Proof. exact (@lem3921156 (term14 _100951)). Qed.
Lemma lem3921158 {_100951 : Type'} : (term16 _100951) = (term14 _100951).
Proof. exact (SYM (@lem3921157 _100951)). Qed.
Lemma lem3921159 {_100951 : Type'} (h1 : term17 _100951) : term17 _100951.
Proof. exact (h1). Qed.
Lemma lem3921162 {_100951 : Type'} (h1 : term16 _100951) : term16 _100951.
Proof. exact (h1). Qed.
Lemma lem3921163 {_100951 : Type'} : term18 _100951.
Proof. exact (fun h0 : term16 _100951 => @lem3921162 _100951 h0). Qed.
Lemma lem3921164 {_100951 : Type'} (h1 : term18 _100951) : term18 _100951.
Proof. exact (h1). Qed.
Lemma lem3921165 {_100951 : Type'} (h1 : term16 _100951) : term16 _100951.
Proof. exact (h1). Qed.
Lemma lem3921166 {_100951 : Type'} (h1 : term16 _100951) (h2 : term18 _100951) : term16 _100951.
Proof. exact (@lem3921164 _100951 h2 (@lem3921165 _100951 h1)). Qed.
Lemma lem3921167 {_100951 : Type'} (h1 : term16 _100951) : term19 _100951.
Proof. exact (fun h0 : term18 _100951 => @lem3921166 _100951 h1 h0). Qed.
Lemma lem3921168 {_100951 : Type'} (h1 : term18 _100951) : term18 _100951.
Proof. exact (h1). Qed.
Lemma lem3921169 {_100951 : Type'} (h1 : term16 _100951) (h2 : term18 _100951) : term16 _100951.
Proof. exact (@lem3921167 _100951 h1 (@lem3921168 _100951 h2)). Qed.
Lemma lem3921170 {_100951 : Type'} (h1 : term18 _100951) : term18 _100951.
Proof. exact (fun h0 : term16 _100951 => @lem3921169 _100951 h0 h1). Qed.
Lemma lem3921171 {_100951 : Type'} : term20 _100951.
Proof. exact (fun h0 : term18 _100951 => @lem3921170 _100951 h0). Qed.
Lemma lem3921174 {_100951 : Type'} : term18 _100951.
Proof. exact (@lem3921171 _100951 (@lem3921163 _100951)). Qed.
Lemma lem3921175 {_100951 : Type'} : term18 _100951.
Proof. exact (@lem3921174 _100951). Qed.
Lemma lem3921177 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3921178 {_100951 : Type'} : (term16 _100951) = (term21 _100951).
Proof. exact (@lem3921177 (term17 _100951)). Qed.
Lemma lem3921180 (t : Prop) : (term22 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3921181 {_100951 : Type'} : (term21 _100951) = (term14 _100951).
Proof. exact (@lem3921180 (term14 _100951)). Qed.
Lemma lem3921200 {_100951 : Type'} : (term16 _100951) = (term14 _100951).
Proof. exact (TRANS (@lem3921178 _100951) (@lem3921181 _100951)). Qed.
Lemma lem3921217 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term6 _100951 a b) = (term6 _100951 a b).
Proof. exact (eq_refl (term6 _100951 a b)). Qed.
Lemma lem3921218 {_100951 : Type'} (a : _100951 -> Prop) : (term8 _100951 a) = (term8 _100951 a).
Proof. exact (fun_ext (fun b : _100951 -> Prop => @lem3921217 _100951 a b)). Qed.
Lemma lem3921219 {_100951 : Type'} : (@all (_100951 -> Prop)) = (@all (_100951 -> Prop)).
Proof. exact (eq_refl (@all (_100951 -> Prop))). Qed.
Lemma lem3921220 {_100951 : Type'} (a : _100951 -> Prop) : (term10 _100951 a) = (term10 _100951 a).
Proof. exact (MK_COMB (@lem3921219 _100951) (@lem3921218 _100951 a)). Qed.
Lemma lem3921221 {_100951 : Type'} : (term12 _100951) = (term12 _100951).
Proof. exact (fun_ext (fun a : _100951 -> Prop => @lem3921220 _100951 a)). Qed.
Lemma lem3921222 {_100951 : Type'} : (@all (_100951 -> Prop)) = (@all (_100951 -> Prop)).
Proof. exact (eq_refl (@all (_100951 -> Prop))). Qed.
Lemma lem3921223 {_100951 : Type'} : (term14 _100951) = (term14 _100951).
Proof. exact (MK_COMB (@lem3921222 _100951) (@lem3921221 _100951)). Qed.
Lemma lem3921244 {_100951 : Type'} : (term16 _100951) = (term14 _100951).
Proof. exact (TRANS (@lem3921200 _100951) (@lem3921223 _100951)). Qed.
Lemma lem3921245 {_100951 : Type'} : (term14 _100951) = (term16 _100951).
Proof. exact (SYM (@lem3921244 _100951)). Qed.
Lemma lem3921248 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3921249 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term3 _100951 a b) = (term23 _100951 a b).
Proof. exact (@lem3921248 (term3 _100951 a b)). Qed.
Lemma lem3921250 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term23 _100951 a b) = (term3 _100951 a b).
Proof. exact (SYM (@lem3921249 _100951 a b)). Qed.
Lemma lem3921251 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) : term24 _100951 a b.
Proof. exact (h1). Qed.
Lemma lem3921261 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term25 _100951 a b.
Proof. exact (h1). Qed.
Lemma lem3921265 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term26 _100951 a b) = (a = b).
Proof. exact (@lem16933 (a = b)). Qed.
Lemma lem3921267 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term27 _100951 a b) = (term27 _100951 a b).
Proof. exact (eq_refl (term27 _100951 a b)). Qed.
Lemma lem3921268 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term28 _100951 a b) = (term29 _100951 a b).
Proof. exact (MK_COMB (@lem3921267 _100951 a b) (@lem3921265 _100951 a b)). Qed.
Lemma lem3921269 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term24 _100951 a b) = (term28 _100951 a b).
Proof. exact (@lem17045 (@SUBSET _100951 a b) (term30 _100951 a b)). Qed.
Lemma lem3921274 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term24 _100951 a b) = (term29 _100951 a b).
Proof. exact (TRANS (@lem3921269 _100951 a b) (@lem3921268 _100951 a b)). Qed.
Lemma lem3921295 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term25 _100951 a b.
Proof. exact (h1). Qed.
Lemma lem3921311 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) : term29 _100951 a b.
Proof. exact (EQ_MP (@lem3921274 _100951 a b) (@lem3921251 _100951 a b h1)). Qed.
Lemma lem3921327 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) : term31 _100951 a b.
Proof. exact (h1). Qed.
Lemma lem3921339 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3921345 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) : term31 _100951 a b.
Proof. exact (h1). Qed.
Lemma lem3921349 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term32 _100951 a b.
Proof. exact (proj2 (@lem3921295 _100951 a b h1)). Qed.
Lemma lem3921351 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3921379 {_100951 : Type'} (b : _100951 -> Prop) : (term33 _100951 b) = (term33 _100951 b).
Proof. exact (eq_refl (term33 _100951 b)). Qed.
Lemma lem3921380 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : a = b) : (term34 _100951 b a) = (term35 _100951 b).
Proof. exact (MK_COMB (@lem3921379 _100951 b) (@lem3921351 _100951 a b h1)). Qed.
Lemma lem3921381 {_100951 : Type'} (b : _100951 -> Prop) : (term35 _100951 b) = (term36 _100951 b).
Proof. exact (eq_refl (term35 _100951 b)). Qed.
Lemma lem3921382 {_100951 : Type'} (b : _100951 -> Prop) (a : _100951 -> Prop) : (term37 _100951 b a) = (term37 _100951 b a).
Proof. exact (eq_refl (term37 _100951 b a)). Qed.
Lemma lem3921383 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : ((term34 _100951 b a) = (term35 _100951 b)) = ((term34 _100951 b a) = (term36 _100951 b)).
Proof. exact (MK_COMB (@lem3921382 _100951 b a) (@lem3921381 _100951 b)). Qed.
Lemma lem3921384 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term34 _100951 b a) = (term32 _100951 a b).
Proof. exact (eq_refl (term34 _100951 b a)). Qed.
Lemma lem3921385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3921386 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term37 _100951 b a) = (term38 _100951 a b).
Proof. exact (MK_COMB (@lem3921385) (@lem3921384 _100951 a b)). Qed.
Lemma lem3921387 {_100951 : Type'} (b : _100951 -> Prop) : (term36 _100951 b) = (term36 _100951 b).
Proof. exact (eq_refl (term36 _100951 b)). Qed.
Lemma lem3921388 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : ((term34 _100951 b a) = (term36 _100951 b)) = ((term32 _100951 a b) = (term36 _100951 b)).
Proof. exact (MK_COMB (@lem3921386 _100951 a b) (@lem3921387 _100951 b)). Qed.
Lemma lem3921389 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : ((term34 _100951 b a) = (term35 _100951 b)) = ((term32 _100951 a b) = (term36 _100951 b)).
Proof. exact (TRANS (@lem3921383 _100951 a b) (@lem3921388 _100951 a b)). Qed.
Lemma lem3921390 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : a = b) : (term32 _100951 a b) = (term36 _100951 b).
Proof. exact (EQ_MP (@lem3921389 _100951 a b) (@lem3921380 _100951 a b h1)). Qed.
Lemma lem3921391 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : term36 _100951 b.
Proof. exact (EQ_MP (@lem3921390 _100951 a b h2) (@lem3921349 _100951 a b h1)). Qed.
Lemma lem3921424 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : @SUBSET _100951 a b.
Proof. exact (proj1 (@lem3921295 _100951 a b h1)). Qed.
Lemma lem3921425 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term39 _100951 a b.
Proof. exact (fun h0 : term31 _100951 a b => @lem3921424 _100951 a b h1). Qed.
Lemma lem3921427 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3921428 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term39 _100951 a b) = (@SUBSET _100951 a b).
Proof. exact (@lem3921427 (@SUBSET _100951 a b)). Qed.
Lemma lem3921429 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : @SUBSET _100951 a b.
Proof. exact (EQ_MP (@lem3921428 _100951 a b) (@lem3921425 _100951 a b h1)). Qed.
Lemma lem3921432 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3921434 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : (term31 _100951 a b) = (term41 _100951 a b).
Proof. exact (@lem3921432 (@SUBSET _100951 a b)). Qed.
Lemma lem3921437 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) : term41 _100951 a b.
Proof. exact (EQ_MP (@lem3921434 _100951 a b) (@lem3921345 _100951 a b h1)). Qed.
Lemma lem3921440 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (@lem3921437 _100951 a b h1 (@lem3921429 _100951 a b h2)). Qed.
Lemma lem3921441 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : term42.
Proof. exact (fun h0 : ~ False => @lem3921440 _100951 a b h1 h2). Qed.
Lemma lem3921443 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3921444 : term42 = False.
Proof. exact (@lem3921443 False). Qed.
Lemma lem3921445 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921444) (@lem3921441 _100951 a b h1 h2)). Qed.
Lemma lem3921478 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3921479 {_100951 : Type'} (b : _100951 -> Prop) : (@CARD _100951 b) = (@CARD _100951 b).
Proof. exact (@lem3921478 (@CARD _100951 b)). Qed.
Lemma lem3921480 {_100951 : Type'} (b : _100951 -> Prop) : term43 _100951 b.
Proof. exact (fun h0 : term36 _100951 b => @lem3921479 _100951 b). Qed.
Lemma lem3921482 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3921483 {_100951 : Type'} (b : _100951 -> Prop) : (term43 _100951 b) = ((@CARD _100951 b) = (@CARD _100951 b)).
Proof. exact (@lem3921482 ((@CARD _100951 b) = (@CARD _100951 b))). Qed.
Lemma lem3921484 {_100951 : Type'} (b : _100951 -> Prop) : (@CARD _100951 b) = (@CARD _100951 b).
Proof. exact (EQ_MP (@lem3921483 _100951 b) (@lem3921480 _100951 b)). Qed.
Lemma lem3921487 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3921489 {_100951 : Type'} (b : _100951 -> Prop) : (term36 _100951 b) = (term44 _100951 b).
Proof. exact (@lem3921487 ((@CARD _100951 b) = (@CARD _100951 b))). Qed.
Lemma lem3921492 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : term44 _100951 b.
Proof. exact (EQ_MP (@lem3921489 _100951 b) (@lem3921391 _100951 a b h1 h2)). Qed.
Lemma lem3921495 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : False.
Proof. exact (@lem3921492 _100951 a b h1 h2 (@lem3921484 _100951 b)). Qed.
Lemma lem3921496 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : term42.
Proof. exact (fun h0 : ~ False => @lem3921495 _100951 a b h1 h2). Qed.
Lemma lem3921498 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3921499 : term42 = False.
Proof. exact (@lem3921498 False). Qed.
Lemma lem3921501 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3921499) (@lem3921496 _100951 a b h1 h2)). Qed.
Lemma lem3921502 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3921501 _100951 a b h1 h2) (fun h3 : False => @lem3921351 _100951 a b h2)). Qed.
Lemma lem3921503 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3921502 _100951 a b h1 h2) (@lem3921351 _100951 a b h2)). Qed.
Lemma lem3921504 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : (term31 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term31 _100951 a b => @lem3921445 _100951 a b h1 h2) (fun h3 : False => @lem3921345 _100951 a b h1)). Qed.
Lemma lem3921505 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921504 _100951 a b h1 h2) (@lem3921345 _100951 a b h1)). Qed.
Lemma lem3921506 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3921503 _100951 a b h1 h2) (fun h3 : False => @lem3921339 _100951 a b h2)). Qed.
Lemma lem3921507 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3921506 _100951 a b h1 h2) (@lem3921339 _100951 a b h2)). Qed.
Lemma lem3921508 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : (term31 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term31 _100951 a b => @lem3921505 _100951 a b h1 h2) (fun h3 : False => @lem3921327 _100951 a b h1)). Qed.
Lemma lem3921509 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921508 _100951 a b h1 h2) (@lem3921327 _100951 a b h1)). Qed.
Lemma lem3921510 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3921507 _100951 a b h1 h2) (fun h3 : False => @lem3921339 _100951 a b h2)). Qed.
Lemma lem3921511 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3921510 _100951 a b h1 h2) (@lem3921339 _100951 a b h2)). Qed.
Lemma lem3921512 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : (term31 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term31 _100951 a b => @lem3921509 _100951 a b h1 h2) (fun h3 : False => @lem3921327 _100951 a b h1)). Qed.
Lemma lem3921513 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term31 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921512 _100951 a b h1 h2) (@lem3921327 _100951 a b h1)). Qed.
Lemma lem3921514 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (or_elim (@lem3921311 _100951 a b h1) (fun h0 : term31 _100951 a b => @lem3921513 _100951 a b h0 h2) (fun h0 : a = b => @lem3921511 _100951 a b h2 h0)). Qed.
Lemma lem3921515 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : (term25 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term25 _100951 a b => @lem3921514 _100951 a b h1 h2) (fun h3 : False => @lem3921295 _100951 a b h2)). Qed.
Lemma lem3921516 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921515 _100951 a b h1 h2) (@lem3921295 _100951 a b h2)). Qed.
Lemma lem3921517 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : (term25 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term25 _100951 a b => @lem3921516 _100951 a b h1 h2) (fun h3 : False => @lem3921261 _100951 a b h2)). Qed.
Lemma lem3921518 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921517 _100951 a b h1 h2) (@lem3921261 _100951 a b h2)). Qed.
Lemma lem3921519 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : (term24 _100951 a b) = False.
Proof. exact (prop_ext (fun h3 : term24 _100951 a b => @lem3921518 _100951 a b h1 h2) (fun h3 : False => @lem3921251 _100951 a b h1)). Qed.
Lemma lem3921520 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term24 _100951 a b) (h2 : term25 _100951 a b) : False.
Proof. exact (EQ_MP (@lem3921519 _100951 a b h1 h2) (@lem3921251 _100951 a b h1)). Qed.
Lemma lem3921521 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term23 _100951 a b.
Proof. exact (fun h0 : term24 _100951 a b => @lem3921520 _100951 a b h0 h1). Qed.
Lemma lem3921522 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) (h1 : term25 _100951 a b) : term3 _100951 a b.
Proof. exact (EQ_MP (@lem3921250 _100951 a b) (@lem3921521 _100951 a b h1)). Qed.
Lemma lem3921523 {_100951 : Type'} (a : _100951 -> Prop) (b : _100951 -> Prop) : term6 _100951 a b.
Proof. exact (fun h0 : term25 _100951 a b => @lem3921522 _100951 a b h0). Qed.
Lemma lem3921528 {_100951 : Type'} (a : _100951 -> Prop) : term10 _100951 a.
Proof. exact (fun b : _100951 -> Prop => @lem3921523 _100951 a b). Qed.
Lemma lem3921533 {_100951 : Type'} : term14 _100951.
Proof. exact (fun a : _100951 -> Prop => @lem3921528 _100951 a). Qed.
Lemma lem3921534 {_100951 : Type'} : term16 _100951.
Proof. exact (EQ_MP (@lem3921245 _100951) (@lem3921533 _100951)). Qed.
Lemma lem3921536 {_100951 : Type'} : term16 _100951.
Proof. exact (@lem3921175 _100951 (@lem3921534 _100951)). Qed.
Lemma lem3921537 {_100951 : Type'} (h1 : term17 _100951) : False.
Proof. exact (@lem3921536 _100951 (@lem3921159 _100951 h1)). Qed.
Lemma lem3921538 {_100951 : Type'} (h1 : term17 _100951) : (term17 _100951) = False.
Proof. exact (prop_ext (fun h2 : term17 _100951 => @lem3921537 _100951 h1) (fun h2 : False => @lem3921159 _100951 h1)). Qed.
Lemma lem3921539 {_100951 : Type'} (h1 : term17 _100951) : False.
Proof. exact (EQ_MP (@lem3921538 _100951 h1) (@lem3921159 _100951 h1)). Qed.
Lemma lem3921540 {_100951 : Type'} : term16 _100951.
Proof. exact (fun h0 : term17 _100951 => @lem3921539 _100951 h0). Qed.
Lemma lem3921541 {_100951 : Type'} : term14 _100951.
Proof. exact (EQ_MP (@lem3921158 _100951) (@lem3921540 _100951)). Qed.
Lemma lem3921542 {_100951 : Type'} : term13 _100951.
Proof. exact (EQ_MP (@lem3921154 _100951) (@lem3921541 _100951)). Qed.
