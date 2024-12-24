Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SUBSET_IMAGE_term_abbrevs.
Require Import CARD_IMAGE_LE_spec.
Require Import CARD_SUBSET_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4015147 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4015148 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4015149 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4015148 t1) (@lem4015147 t1)). Qed.
Lemma lem4015150 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4015149 t1 t2). Qed.
Lemma lem4015151 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4015152 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4015151 t1 t2) (@lem4015150 t1 t2)). Qed.
Lemma lem4015153 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4015152 t1 t2 t3). Qed.
Lemma lem4015154 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4015155 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4015154 t1 t2 t3) (@lem4015153 t1 t2 t3)). Qed.
Lemma lem4015156 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4015155 t1 t2 t3)). Qed.
Lemma lem4015158 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4015159 {_101783 _101790 : Type'} : (term8 _101783 _101790) = (term9 _101783 _101790).
Proof. exact (@lem4015158 (term8 _101783 _101790)). Qed.
Lemma lem4015160 {_101783 _101790 : Type'} : (term9 _101783 _101790) = (term8 _101783 _101790).
Proof. exact (SYM (@lem4015159 _101783 _101790)). Qed.
Lemma lem4015161 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : term10 _101783 _101790.
Proof. exact (h1). Qed.
Lemma lem4015162 {_101783 B : Type'} : term11 _101783 B.
Proof. exact (@lem3615104 _101783 B). Qed.
Lemma lem4015163 {_101783 A : Type'} : term12 _101783 A.
Proof. exact (@lem3615104 A _101783). Qed.
Lemma lem4015164 {_101783 _101790 : Type'} : term11 _101783 _101790.
Proof. exact (@lem3615104 _101783 _101790). Qed.
Lemma lem4015165 {_101783 B : Type'} : term13 _101783 B.
Proof. exact (@lem4008003 _101783 B). Qed.
Lemma lem4015166 {A B : Type'} : term13 A B.
Proof. exact (@lem4008003 A B). Qed.
Lemma lem4015167 {B : Type'} : term14 B.
Proof. exact (@lem4008003 B B). Qed.
Lemma lem4015168 {_101790 B : Type'} : term13 _101790 B.
Proof. exact (@lem4008003 _101790 B). Qed.
Lemma lem4015169 {_101790 A : Type'} : term15 _101790 A.
Proof. exact (@lem4008003 A _101790). Qed.
Lemma lem4015170 {_101783 A : Type'} : term15 _101783 A.
Proof. exact (@lem4008003 A _101783). Qed.
Lemma lem4015171 {_101783 _101790 : Type'} : term13 _101783 _101790.
Proof. exact (@lem4008003 _101783 _101790). Qed.
Lemma lem4015176 {_101790 : Type'} : term16 _101790.
Proof. exact (@lem3902682 _101790). Qed.
Lemma lem4015177 {_101783 : Type'} : term16 _101783.
Proof. exact (@lem3902682 _101783). Qed.
Lemma lem4015178 {A : Type'} : term16 A.
Proof. exact (@lem3902682 A). Qed.
Lemma lem4015179 {B : Type'} : term16 B.
Proof. exact (@lem3902682 B). Qed.
Lemma lem4015187 {_101783 _101790 A B : Type'} (h1 : term17 _101783 _101790 A B) : term17 _101783 _101790 A B.
Proof. exact (h1). Qed.
Lemma lem4015188 {_101783 _101790 A B : Type'} : term18 _101783 _101790 A B.
Proof. exact (fun h0 : term17 _101783 _101790 A B => @lem4015187 _101783 _101790 A B h0). Qed.
Lemma lem4015189 {_101783 _101790 A B : Type'} (h1 : term18 _101783 _101790 A B) : term18 _101783 _101790 A B.
Proof. exact (h1). Qed.
Lemma lem4015190 {_101783 _101790 A B : Type'} (h1 : term17 _101783 _101790 A B) : term17 _101783 _101790 A B.
Proof. exact (h1). Qed.
Lemma lem4015191 {_101783 _101790 A B : Type'} (h1 : term17 _101783 _101790 A B) (h2 : term18 _101783 _101790 A B) : term17 _101783 _101790 A B.
Proof. exact (@lem4015189 _101783 _101790 A B h2 (@lem4015190 _101783 _101790 A B h1)). Qed.
Lemma lem4015192 {_101783 _101790 A B : Type'} (h1 : term17 _101783 _101790 A B) : term19 _101783 _101790 A B.
Proof. exact (fun h0 : term18 _101783 _101790 A B => @lem4015191 _101783 _101790 A B h1 h0). Qed.
Lemma lem4015193 {_101783 _101790 A B : Type'} (h1 : term18 _101783 _101790 A B) : term18 _101783 _101790 A B.
Proof. exact (h1). Qed.
Lemma lem4015194 {_101783 _101790 A B : Type'} (h1 : term17 _101783 _101790 A B) (h2 : term18 _101783 _101790 A B) : term17 _101783 _101790 A B.
Proof. exact (@lem4015192 _101783 _101790 A B h1 (@lem4015193 _101783 _101790 A B h2)). Qed.
Lemma lem4015195 {_101783 _101790 A B : Type'} (h1 : term18 _101783 _101790 A B) : term18 _101783 _101790 A B.
Proof. exact (fun h0 : term17 _101783 _101790 A B => @lem4015194 _101783 _101790 A B h0 h1). Qed.
Lemma lem4015196 {_101783 _101790 A B : Type'} : term20 _101783 _101790 A B.
Proof. exact (fun h0 : term18 _101783 _101790 A B => @lem4015195 _101783 _101790 A B h0). Qed.
Lemma lem4015199 {_101783 _101790 A B : Type'} : term18 _101783 _101790 A B.
Proof. exact (@lem4015196 _101783 _101790 A B (@lem4015188 _101783 _101790 A B)). Qed.
Lemma lem4015200 {_101783 _101790 A B : Type'} : term18 _101783 _101790 A B.
Proof. exact (@lem4015199 _101783 _101790 A B). Qed.
Lemma lem4015396 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4015397 : term21 = term22.
Proof. exact (@lem4015396 term23). Qed.
Lemma lem4015414 {_101783 A : Type'} : (term24 _101783 A) = (term24 _101783 A).
Proof. exact (eq_refl (term24 _101783 A)). Qed.
Lemma lem4015415 {_101783 A : Type'} : (term25 _101783 A) = (term26 _101783 A).
Proof. exact (MK_COMB (@lem4015414 _101783 A) (@lem4015397)). Qed.
Lemma lem4015418 {_101783 B : Type'} : (term27 _101783 B) = (term27 _101783 B).
Proof. exact (eq_refl (term27 _101783 B)). Qed.
Lemma lem4015419 {_101783 A B : Type'} : (term28 _101783 A B) = (term29 _101783 A B).
Proof. exact (MK_COMB (@lem4015418 _101783 B) (@lem4015415 _101783 A)). Qed.
Lemma lem4015422 {_101783 _101790 : Type'} : (term27 _101783 _101790) = (term27 _101783 _101790).
Proof. exact (eq_refl (term27 _101783 _101790)). Qed.
Lemma lem4015423 {_101783 _101790 A B : Type'} : (term30 _101783 _101790 A B) = (term31 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015422 _101783 _101790) (@lem4015419 _101783 A B)). Qed.
Lemma lem4015426 {B : Type'} : (term32 B) = (term32 B).
Proof. exact (eq_refl (term32 B)). Qed.
Lemma lem4015427 {_101783 _101790 A B : Type'} : (term33 _101783 _101790 A B) = (term34 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015426 B) (@lem4015423 _101783 _101790 A B)). Qed.
Lemma lem4015430 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (eq_refl (term35 A B)). Qed.
Lemma lem4015431 {_101783 _101790 A B : Type'} : (term36 _101783 _101790 A B) = (term37 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015430 A B) (@lem4015427 _101783 _101790 A B)). Qed.
Lemma lem4015434 {_101790 A : Type'} : (term38 _101790 A) = (term38 _101790 A).
Proof. exact (eq_refl (term38 _101790 A)). Qed.
Lemma lem4015435 {_101783 _101790 A B : Type'} : (term39 _101783 _101790 A B) = (term40 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015434 _101790 A) (@lem4015431 _101783 _101790 A B)). Qed.
Lemma lem4015438 {_101783 A : Type'} : (term38 _101783 A) = (term38 _101783 A).
Proof. exact (eq_refl (term38 _101783 A)). Qed.
Lemma lem4015439 {_101783 _101790 A B : Type'} : (term41 _101783 _101790 A B) = (term42 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015438 _101783 A) (@lem4015435 _101783 _101790 A B)). Qed.
Lemma lem4015442 {_101790 B : Type'} : (term35 _101790 B) = (term35 _101790 B).
Proof. exact (eq_refl (term35 _101790 B)). Qed.
Lemma lem4015443 {_101783 _101790 A B : Type'} : (term43 _101783 _101790 A B) = (term44 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015442 _101790 B) (@lem4015439 _101783 _101790 A B)). Qed.
Lemma lem4015446 {_101783 B : Type'} : (term35 _101783 B) = (term35 _101783 B).
Proof. exact (eq_refl (term35 _101783 B)). Qed.
Lemma lem4015447 {_101783 _101790 A B : Type'} : (term45 _101783 _101790 A B) = (term46 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015446 _101783 B) (@lem4015443 _101783 _101790 A B)). Qed.
Lemma lem4015450 {_101783 _101790 : Type'} : (term35 _101783 _101790) = (term35 _101783 _101790).
Proof. exact (eq_refl (term35 _101783 _101790)). Qed.
Lemma lem4015451 {_101783 _101790 A B : Type'} : (term47 _101783 _101790 A B) = (term48 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015450 _101783 _101790) (@lem4015447 _101783 _101790 A B)). Qed.
Lemma lem4015454 {B : Type'} : (term49 B) = (term49 B).
Proof. exact (eq_refl (term49 B)). Qed.
Lemma lem4015455 {_101783 _101790 A B : Type'} : (term50 _101783 _101790 A B) = (term51 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015454 B) (@lem4015451 _101783 _101790 A B)). Qed.
Lemma lem4015458 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (eq_refl (term49 A)). Qed.
Lemma lem4015459 {_101783 _101790 A B : Type'} : (term52 _101783 _101790 A B) = (term53 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015458 A) (@lem4015455 _101783 _101790 A B)). Qed.
Lemma lem4015462 {_101790 : Type'} : (term49 _101790) = (term49 _101790).
Proof. exact (eq_refl (term49 _101790)). Qed.
Lemma lem4015463 {_101783 _101790 A B : Type'} : (term54 _101783 _101790 A B) = (term55 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015462 _101790) (@lem4015459 _101783 _101790 A B)). Qed.
Lemma lem4015466 {_101783 : Type'} : (term49 _101783) = (term49 _101783).
Proof. exact (eq_refl (term49 _101783)). Qed.
Lemma lem4015467 {_101783 _101790 A B : Type'} : (term56 _101783 _101790 A B) = (term57 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015466 _101783) (@lem4015463 _101783 _101790 A B)). Qed.
Lemma lem4015470 {_101783 _101790 : Type'} : (term58 _101783 _101790) = (term58 _101783 _101790).
Proof. exact (eq_refl (term58 _101783 _101790)). Qed.
Lemma lem4015477 {_101783 _101790 A B : Type'} : (term17 _101783 _101790 A B) = (term59 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015470 _101783 _101790) (@lem4015467 _101783 _101790 A B)). Qed.
Lemma lem4015486 (n : nat) (m : nat) (p : nat) : (term60 n m p) = (term60 n m p).
Proof. exact (eq_refl (term60 n m p)). Qed.
Lemma lem4015487 (n : nat) (m : nat) : (term61 n m) = (term61 n m).
Proof. exact (fun_ext (fun p : nat => @lem4015486 n m p)). Qed.
Lemma lem4015488 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4015489 (n : nat) (m : nat) : (term62 n m) = (term62 n m).
Proof. exact (MK_COMB (@lem4015488) (@lem4015487 n m)). Qed.
Lemma lem4015490 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem4015489 n m)). Qed.
Lemma lem4015491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4015492 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem4015491) (@lem4015490 m)). Qed.
Lemma lem4015493 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem4015492 m)). Qed.
Lemma lem4015494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4015495 : term23 = term23.
Proof. exact (MK_COMB (@lem4015494) (@lem4015493)). Qed.
Lemma lem4015496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4015497 : term22 = term22.
Proof. exact (MK_COMB (@lem4015496) (@lem4015495)). Qed.
Lemma lem4015502 {_101783 A : Type'} (f : A -> _101783) (s : A -> Prop) : (term66 _101783 A f s) = (term66 _101783 A f s).
Proof. exact (eq_refl (term66 _101783 A f s)). Qed.
Lemma lem4015503 {_101783 A : Type'} (f : A -> _101783) : (term67 _101783 A f) = (term67 _101783 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4015502 _101783 A f s)). Qed.
Lemma lem4015504 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015505 {_101783 A : Type'} (f : A -> _101783) : (term68 _101783 A f) = (term68 _101783 A f).
Proof. exact (MK_COMB (@lem4015504 A) (@lem4015503 _101783 A f)). Qed.
Lemma lem4015506 {_101783 A : Type'} : (term69 _101783 A) = (term69 _101783 A).
Proof. exact (fun_ext (fun f : A -> _101783 => @lem4015505 _101783 A f)). Qed.
Lemma lem4015507 {_101783 A : Type'} : (@all (A -> _101783)) = (@all (A -> _101783)).
Proof. exact (eq_refl (@all (A -> _101783))). Qed.
Lemma lem4015508 {_101783 A : Type'} : (term12 _101783 A) = (term12 _101783 A).
Proof. exact (MK_COMB (@lem4015507 _101783 A) (@lem4015506 _101783 A)). Qed.
Lemma lem4015509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015510 {_101783 A : Type'} : (term24 _101783 A) = (term24 _101783 A).
Proof. exact (MK_COMB (@lem4015509) (@lem4015508 _101783 A)). Qed.
Lemma lem4015511 {_101783 A : Type'} : (term26 _101783 A) = (term26 _101783 A).
Proof. exact (MK_COMB (@lem4015510 _101783 A) (@lem4015497)). Qed.
Lemma lem4015516 {_101783 B : Type'} (f : _101783 -> B) (s : _101783 -> Prop) : (term70 _101783 B f s) = (term70 _101783 B f s).
Proof. exact (eq_refl (term70 _101783 B f s)). Qed.
Lemma lem4015517 {_101783 B : Type'} (f : _101783 -> B) : (term71 _101783 B f) = (term71 _101783 B f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4015516 _101783 B f s)). Qed.
Lemma lem4015518 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015519 {_101783 B : Type'} (f : _101783 -> B) : (term72 _101783 B f) = (term72 _101783 B f).
Proof. exact (MK_COMB (@lem4015518 _101783) (@lem4015517 _101783 B f)). Qed.
Lemma lem4015520 {_101783 B : Type'} : (term73 _101783 B) = (term73 _101783 B).
Proof. exact (fun_ext (fun f : _101783 -> B => @lem4015519 _101783 B f)). Qed.
Lemma lem4015521 {_101783 B : Type'} : (@all (_101783 -> B)) = (@all (_101783 -> B)).
Proof. exact (eq_refl (@all (_101783 -> B))). Qed.
Lemma lem4015522 {_101783 B : Type'} : (term11 _101783 B) = (term11 _101783 B).
Proof. exact (MK_COMB (@lem4015521 _101783 B) (@lem4015520 _101783 B)). Qed.
Lemma lem4015523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015524 {_101783 B : Type'} : (term27 _101783 B) = (term27 _101783 B).
Proof. exact (MK_COMB (@lem4015523) (@lem4015522 _101783 B)). Qed.
Lemma lem4015525 {_101783 A B : Type'} : (term29 _101783 A B) = (term29 _101783 A B).
Proof. exact (MK_COMB (@lem4015524 _101783 B) (@lem4015511 _101783 A)). Qed.
Lemma lem4015530 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term70 _101783 _101790 f s) = (term70 _101783 _101790 f s).
Proof. exact (eq_refl (term70 _101783 _101790 f s)). Qed.
Lemma lem4015531 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term71 _101783 _101790 f) = (term71 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4015530 _101783 _101790 f s)). Qed.
Lemma lem4015532 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015533 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term72 _101783 _101790 f) = (term72 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4015532 _101783) (@lem4015531 _101783 _101790 f)). Qed.
Lemma lem4015534 {_101783 _101790 : Type'} : (term73 _101783 _101790) = (term73 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4015533 _101783 _101790 f)). Qed.
Lemma lem4015535 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4015536 {_101783 _101790 : Type'} : (term11 _101783 _101790) = (term11 _101783 _101790).
Proof. exact (MK_COMB (@lem4015535 _101783 _101790) (@lem4015534 _101783 _101790)). Qed.
Lemma lem4015537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015538 {_101783 _101790 : Type'} : (term27 _101783 _101790) = (term27 _101783 _101790).
Proof. exact (MK_COMB (@lem4015537) (@lem4015536 _101783 _101790)). Qed.
Lemma lem4015539 {_101783 _101790 A B : Type'} : (term31 _101783 _101790 A B) = (term31 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015538 _101783 _101790) (@lem4015525 _101783 A B)). Qed.
Lemma lem4015544 {B : Type'} (f : B -> B) (s : B -> Prop) : (term74 B f s) = (term74 B f s).
Proof. exact (eq_refl (term74 B f s)). Qed.
Lemma lem4015545 {B : Type'} (f : B -> B) : (term75 B f) = (term75 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4015544 B f s)). Qed.
Lemma lem4015546 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4015547 {B : Type'} (f : B -> B) : (term76 B f) = (term76 B f).
Proof. exact (MK_COMB (@lem4015546 B) (@lem4015545 B f)). Qed.
Lemma lem4015548 {B : Type'} : (term77 B) = (term77 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4015547 B f)). Qed.
Lemma lem4015549 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4015550 {B : Type'} : (term14 B) = (term14 B).
Proof. exact (MK_COMB (@lem4015549 B) (@lem4015548 B)). Qed.
Lemma lem4015551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015552 {B : Type'} : (term32 B) = (term32 B).
Proof. exact (MK_COMB (@lem4015551) (@lem4015550 B)). Qed.
Lemma lem4015553 {_101783 _101790 A B : Type'} : (term34 _101783 _101790 A B) = (term34 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015552 B) (@lem4015539 _101783 _101790 A B)). Qed.
Lemma lem4015558 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term78 A B f s) = (term78 A B f s).
Proof. exact (eq_refl (term78 A B f s)). Qed.
Lemma lem4015559 {A B : Type'} (f : A -> B) : (term79 A B f) = (term79 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4015558 A B f s)). Qed.
Lemma lem4015560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015561 {A B : Type'} (f : A -> B) : (term80 A B f) = (term80 A B f).
Proof. exact (MK_COMB (@lem4015560 A) (@lem4015559 A B f)). Qed.
Lemma lem4015562 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4015561 A B f)). Qed.
Lemma lem4015563 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4015564 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem4015563 A B) (@lem4015562 A B)). Qed.
Lemma lem4015565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015566 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem4015565) (@lem4015564 A B)). Qed.
Lemma lem4015567 {_101783 _101790 A B : Type'} : (term37 _101783 _101790 A B) = (term37 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015566 A B) (@lem4015553 _101783 _101790 A B)). Qed.
Lemma lem4015572 {_101790 A : Type'} (f : A -> _101790) (s : A -> Prop) : (term82 _101790 A f s) = (term82 _101790 A f s).
Proof. exact (eq_refl (term82 _101790 A f s)). Qed.
Lemma lem4015573 {_101790 A : Type'} (f : A -> _101790) : (term83 _101790 A f) = (term83 _101790 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4015572 _101790 A f s)). Qed.
Lemma lem4015574 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015575 {_101790 A : Type'} (f : A -> _101790) : (term84 _101790 A f) = (term84 _101790 A f).
Proof. exact (MK_COMB (@lem4015574 A) (@lem4015573 _101790 A f)). Qed.
Lemma lem4015576 {_101790 A : Type'} : (term85 _101790 A) = (term85 _101790 A).
Proof. exact (fun_ext (fun f : A -> _101790 => @lem4015575 _101790 A f)). Qed.
Lemma lem4015577 {_101790 A : Type'} : (@all (A -> _101790)) = (@all (A -> _101790)).
Proof. exact (eq_refl (@all (A -> _101790))). Qed.
Lemma lem4015578 {_101790 A : Type'} : (term15 _101790 A) = (term15 _101790 A).
Proof. exact (MK_COMB (@lem4015577 _101790 A) (@lem4015576 _101790 A)). Qed.
Lemma lem4015579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015580 {_101790 A : Type'} : (term38 _101790 A) = (term38 _101790 A).
Proof. exact (MK_COMB (@lem4015579) (@lem4015578 _101790 A)). Qed.
Lemma lem4015581 {_101783 _101790 A B : Type'} : (term40 _101783 _101790 A B) = (term40 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015580 _101790 A) (@lem4015567 _101783 _101790 A B)). Qed.
Lemma lem4015586 {_101783 A : Type'} (f : A -> _101783) (s : A -> Prop) : (term82 _101783 A f s) = (term82 _101783 A f s).
Proof. exact (eq_refl (term82 _101783 A f s)). Qed.
Lemma lem4015587 {_101783 A : Type'} (f : A -> _101783) : (term83 _101783 A f) = (term83 _101783 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4015586 _101783 A f s)). Qed.
Lemma lem4015588 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015589 {_101783 A : Type'} (f : A -> _101783) : (term84 _101783 A f) = (term84 _101783 A f).
Proof. exact (MK_COMB (@lem4015588 A) (@lem4015587 _101783 A f)). Qed.
Lemma lem4015590 {_101783 A : Type'} : (term85 _101783 A) = (term85 _101783 A).
Proof. exact (fun_ext (fun f : A -> _101783 => @lem4015589 _101783 A f)). Qed.
Lemma lem4015591 {_101783 A : Type'} : (@all (A -> _101783)) = (@all (A -> _101783)).
Proof. exact (eq_refl (@all (A -> _101783))). Qed.
Lemma lem4015592 {_101783 A : Type'} : (term15 _101783 A) = (term15 _101783 A).
Proof. exact (MK_COMB (@lem4015591 _101783 A) (@lem4015590 _101783 A)). Qed.
Lemma lem4015593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015594 {_101783 A : Type'} : (term38 _101783 A) = (term38 _101783 A).
Proof. exact (MK_COMB (@lem4015593) (@lem4015592 _101783 A)). Qed.
Lemma lem4015595 {_101783 _101790 A B : Type'} : (term42 _101783 _101790 A B) = (term42 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015594 _101783 A) (@lem4015581 _101783 _101790 A B)). Qed.
Lemma lem4015600 {_101790 B : Type'} (f : _101790 -> B) (s : _101790 -> Prop) : (term78 _101790 B f s) = (term78 _101790 B f s).
Proof. exact (eq_refl (term78 _101790 B f s)). Qed.
Lemma lem4015601 {_101790 B : Type'} (f : _101790 -> B) : (term79 _101790 B f) = (term79 _101790 B f).
Proof. exact (fun_ext (fun s : _101790 -> Prop => @lem4015600 _101790 B f s)). Qed.
Lemma lem4015602 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4015603 {_101790 B : Type'} (f : _101790 -> B) : (term80 _101790 B f) = (term80 _101790 B f).
Proof. exact (MK_COMB (@lem4015602 _101790) (@lem4015601 _101790 B f)). Qed.
Lemma lem4015604 {_101790 B : Type'} : (term81 _101790 B) = (term81 _101790 B).
Proof. exact (fun_ext (fun f : _101790 -> B => @lem4015603 _101790 B f)). Qed.
Lemma lem4015605 {_101790 B : Type'} : (@all (_101790 -> B)) = (@all (_101790 -> B)).
Proof. exact (eq_refl (@all (_101790 -> B))). Qed.
Lemma lem4015606 {_101790 B : Type'} : (term13 _101790 B) = (term13 _101790 B).
Proof. exact (MK_COMB (@lem4015605 _101790 B) (@lem4015604 _101790 B)). Qed.
Lemma lem4015607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015608 {_101790 B : Type'} : (term35 _101790 B) = (term35 _101790 B).
Proof. exact (MK_COMB (@lem4015607) (@lem4015606 _101790 B)). Qed.
Lemma lem4015609 {_101783 _101790 A B : Type'} : (term44 _101783 _101790 A B) = (term44 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015608 _101790 B) (@lem4015595 _101783 _101790 A B)). Qed.
Lemma lem4015614 {_101783 B : Type'} (f : _101783 -> B) (s : _101783 -> Prop) : (term78 _101783 B f s) = (term78 _101783 B f s).
Proof. exact (eq_refl (term78 _101783 B f s)). Qed.
Lemma lem4015615 {_101783 B : Type'} (f : _101783 -> B) : (term79 _101783 B f) = (term79 _101783 B f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4015614 _101783 B f s)). Qed.
Lemma lem4015616 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015617 {_101783 B : Type'} (f : _101783 -> B) : (term80 _101783 B f) = (term80 _101783 B f).
Proof. exact (MK_COMB (@lem4015616 _101783) (@lem4015615 _101783 B f)). Qed.
Lemma lem4015618 {_101783 B : Type'} : (term81 _101783 B) = (term81 _101783 B).
Proof. exact (fun_ext (fun f : _101783 -> B => @lem4015617 _101783 B f)). Qed.
Lemma lem4015619 {_101783 B : Type'} : (@all (_101783 -> B)) = (@all (_101783 -> B)).
Proof. exact (eq_refl (@all (_101783 -> B))). Qed.
Lemma lem4015620 {_101783 B : Type'} : (term13 _101783 B) = (term13 _101783 B).
Proof. exact (MK_COMB (@lem4015619 _101783 B) (@lem4015618 _101783 B)). Qed.
Lemma lem4015621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015622 {_101783 B : Type'} : (term35 _101783 B) = (term35 _101783 B).
Proof. exact (MK_COMB (@lem4015621) (@lem4015620 _101783 B)). Qed.
Lemma lem4015623 {_101783 _101790 A B : Type'} : (term46 _101783 _101790 A B) = (term46 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015622 _101783 B) (@lem4015609 _101783 _101790 A B)). Qed.
Lemma lem4015628 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term78 _101783 _101790 f s) = (term78 _101783 _101790 f s).
Proof. exact (eq_refl (term78 _101783 _101790 f s)). Qed.
Lemma lem4015629 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term79 _101783 _101790 f) = (term79 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4015628 _101783 _101790 f s)). Qed.
Lemma lem4015630 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015631 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term80 _101783 _101790 f) = (term80 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4015630 _101783) (@lem4015629 _101783 _101790 f)). Qed.
Lemma lem4015632 {_101783 _101790 : Type'} : (term81 _101783 _101790) = (term81 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4015631 _101783 _101790 f)). Qed.
Lemma lem4015633 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4015634 {_101783 _101790 : Type'} : (term13 _101783 _101790) = (term13 _101783 _101790).
Proof. exact (MK_COMB (@lem4015633 _101783 _101790) (@lem4015632 _101783 _101790)). Qed.
Lemma lem4015635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015636 {_101783 _101790 : Type'} : (term35 _101783 _101790) = (term35 _101783 _101790).
Proof. exact (MK_COMB (@lem4015635) (@lem4015634 _101783 _101790)). Qed.
Lemma lem4015637 {_101783 _101790 A B : Type'} : (term48 _101783 _101790 A B) = (term48 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015636 _101783 _101790) (@lem4015623 _101783 _101790 A B)). Qed.
Lemma lem4015646 {B : Type'} (a : B -> Prop) (b : B -> Prop) : (term86 B a b) = (term86 B a b).
Proof. exact (eq_refl (term86 B a b)). Qed.
Lemma lem4015647 {B : Type'} (a : B -> Prop) : (term87 B a) = (term87 B a).
Proof. exact (fun_ext (fun b : B -> Prop => @lem4015646 B a b)). Qed.
Lemma lem4015648 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4015649 {B : Type'} (a : B -> Prop) : (term88 B a) = (term88 B a).
Proof. exact (MK_COMB (@lem4015648 B) (@lem4015647 B a)). Qed.
Lemma lem4015650 {B : Type'} : (term89 B) = (term89 B).
Proof. exact (fun_ext (fun a : B -> Prop => @lem4015649 B a)). Qed.
Lemma lem4015651 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4015652 {B : Type'} : (term16 B) = (term16 B).
Proof. exact (MK_COMB (@lem4015651 B) (@lem4015650 B)). Qed.
Lemma lem4015653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015654 {B : Type'} : (term49 B) = (term49 B).
Proof. exact (MK_COMB (@lem4015653) (@lem4015652 B)). Qed.
Lemma lem4015655 {_101783 _101790 A B : Type'} : (term51 _101783 _101790 A B) = (term51 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015654 B) (@lem4015637 _101783 _101790 A B)). Qed.
Lemma lem4015664 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term86 A a b) = (term86 A a b).
Proof. exact (eq_refl (term86 A a b)). Qed.
Lemma lem4015665 {A : Type'} (a : A -> Prop) : (term87 A a) = (term87 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem4015664 A a b)). Qed.
Lemma lem4015666 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015667 {A : Type'} (a : A -> Prop) : (term88 A a) = (term88 A a).
Proof. exact (MK_COMB (@lem4015666 A) (@lem4015665 A a)). Qed.
Lemma lem4015668 {A : Type'} : (term89 A) = (term89 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4015667 A a)). Qed.
Lemma lem4015669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4015670 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4015669 A) (@lem4015668 A)). Qed.
Lemma lem4015671 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015672 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (MK_COMB (@lem4015671) (@lem4015670 A)). Qed.
Lemma lem4015673 {_101783 _101790 A B : Type'} : (term53 _101783 _101790 A B) = (term53 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015672 A) (@lem4015655 _101783 _101790 A B)). Qed.
Lemma lem4015682 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term86 _101790 a b) = (term86 _101790 a b).
Proof. exact (eq_refl (term86 _101790 a b)). Qed.
Lemma lem4015683 {_101790 : Type'} (a : _101790 -> Prop) : (term87 _101790 a) = (term87 _101790 a).
Proof. exact (fun_ext (fun b : _101790 -> Prop => @lem4015682 _101790 a b)). Qed.
Lemma lem4015684 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4015685 {_101790 : Type'} (a : _101790 -> Prop) : (term88 _101790 a) = (term88 _101790 a).
Proof. exact (MK_COMB (@lem4015684 _101790) (@lem4015683 _101790 a)). Qed.
Lemma lem4015686 {_101790 : Type'} : (term89 _101790) = (term89 _101790).
Proof. exact (fun_ext (fun a : _101790 -> Prop => @lem4015685 _101790 a)). Qed.
Lemma lem4015687 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4015688 {_101790 : Type'} : (term16 _101790) = (term16 _101790).
Proof. exact (MK_COMB (@lem4015687 _101790) (@lem4015686 _101790)). Qed.
Lemma lem4015689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015690 {_101790 : Type'} : (term49 _101790) = (term49 _101790).
Proof. exact (MK_COMB (@lem4015689) (@lem4015688 _101790)). Qed.
Lemma lem4015691 {_101783 _101790 A B : Type'} : (term55 _101783 _101790 A B) = (term55 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015690 _101790) (@lem4015673 _101783 _101790 A B)). Qed.
Lemma lem4015700 {_101783 : Type'} (a : _101783 -> Prop) (b : _101783 -> Prop) : (term86 _101783 a b) = (term86 _101783 a b).
Proof. exact (eq_refl (term86 _101783 a b)). Qed.
Lemma lem4015701 {_101783 : Type'} (a : _101783 -> Prop) : (term87 _101783 a) = (term87 _101783 a).
Proof. exact (fun_ext (fun b : _101783 -> Prop => @lem4015700 _101783 a b)). Qed.
Lemma lem4015702 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015703 {_101783 : Type'} (a : _101783 -> Prop) : (term88 _101783 a) = (term88 _101783 a).
Proof. exact (MK_COMB (@lem4015702 _101783) (@lem4015701 _101783 a)). Qed.
Lemma lem4015704 {_101783 : Type'} : (term89 _101783) = (term89 _101783).
Proof. exact (fun_ext (fun a : _101783 -> Prop => @lem4015703 _101783 a)). Qed.
Lemma lem4015705 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015706 {_101783 : Type'} : (term16 _101783) = (term16 _101783).
Proof. exact (MK_COMB (@lem4015705 _101783) (@lem4015704 _101783)). Qed.
Lemma lem4015707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015708 {_101783 : Type'} : (term49 _101783) = (term49 _101783).
Proof. exact (MK_COMB (@lem4015707) (@lem4015706 _101783)). Qed.
Lemma lem4015709 {_101783 _101790 A B : Type'} : (term57 _101783 _101790 A B) = (term57 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015708 _101783) (@lem4015691 _101783 _101790 A B)). Qed.
Lemma lem4015718 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) : (term90 _101783 _101790 f s t) = (term90 _101783 _101790 f s t).
Proof. exact (eq_refl (term90 _101783 _101790 f s t)). Qed.
Lemma lem4015719 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term91 _101783 _101790 f s) = (term91 _101783 _101790 f s).
Proof. exact (fun_ext (fun t : _101783 -> Prop => @lem4015718 _101783 _101790 f s t)). Qed.
Lemma lem4015720 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4015721 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term92 _101783 _101790 f s) = (term92 _101783 _101790 f s).
Proof. exact (MK_COMB (@lem4015720 _101783) (@lem4015719 _101783 _101790 f s)). Qed.
Lemma lem4015722 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term93 _101783 _101790 f) = (term93 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101790 -> Prop => @lem4015721 _101783 _101790 f s)). Qed.
Lemma lem4015723 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4015724 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term94 _101783 _101790 f) = (term94 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4015723 _101790) (@lem4015722 _101783 _101790 f)). Qed.
Lemma lem4015725 {_101783 _101790 : Type'} : (term95 _101783 _101790) = (term95 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4015724 _101783 _101790 f)). Qed.
Lemma lem4015726 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4015727 {_101783 _101790 : Type'} : (term8 _101783 _101790) = (term8 _101783 _101790).
Proof. exact (MK_COMB (@lem4015726 _101783 _101790) (@lem4015725 _101783 _101790)). Qed.
Lemma lem4015728 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4015729 {_101783 _101790 : Type'} : (term10 _101783 _101790) = (term10 _101783 _101790).
Proof. exact (MK_COMB (@lem4015728) (@lem4015727 _101783 _101790)). Qed.
Lemma lem4015730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4015731 {_101783 _101790 : Type'} : (term58 _101783 _101790) = (term58 _101783 _101790).
Proof. exact (MK_COMB (@lem4015730) (@lem4015729 _101783 _101790)). Qed.
Lemma lem4015732 {_101783 _101790 A B : Type'} : (term59 _101783 _101790 A B) = (term59 _101783 _101790 A B).
Proof. exact (MK_COMB (@lem4015731 _101783 _101790) (@lem4015709 _101783 _101790 A B)). Qed.
Lemma lem4016013 {_101783 _101790 A B : Type'} : (term17 _101783 _101790 A B) = (term59 _101783 _101790 A B).
Proof. exact (TRANS (@lem4015477 _101783 _101790 A B) (@lem4015732 _101783 _101790 A B)). Qed.
Lemma lem4016014 {_101783 _101790 A B : Type'} : (term59 _101783 _101790 A B) = (term17 _101783 _101790 A B).
Proof. exact (SYM (@lem4016013 _101783 _101790 A B)). Qed.
Lemma lem4016015 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : term10 _101783 _101790.
Proof. exact (h1). Qed.
Lemma lem4016017 {_101790 : Type'} (h1 : term16 _101790) : term16 _101790.
Proof. exact (h1). Qed.
Lemma lem4016020 {_101783 _101790 : Type'} (h1 : term13 _101783 _101790) : term13 _101783 _101790.
Proof. exact (h1). Qed.
Lemma lem4016027 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) : term11 _101783 _101790.
Proof. exact (h1). Qed.
Lemma lem4016030 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem4016041 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) : (term96 _101783 _101790 f s t) = (term97 _101783 _101790 f s t).
Proof. exact (@lem17362 (term98 _101783 _101790 s f t) (term99 _101783 _101790 s t)). Qed.
Lemma lem4016042 {_101783 : Type'} (P : type686 _101783) : (term100 _101783 P) = (term101 _101783 P).
Proof. exact (@lem18392 (_101783 -> Prop) P). Qed.
Lemma lem4016043 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term102 _101783 _101790 f s) = (term103 _101783 _101790 f s).
Proof. exact (@lem4016042 _101783 (term91 _101783 _101790 f s)). Qed.
Lemma lem4016044 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) : (term104 _101783 _101790 f s t) = (term90 _101783 _101790 f s t).
Proof. exact (eq_refl (term104 _101783 _101790 f s t)). Qed.
Lemma lem4016045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4016046 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) : (term105 _101783 _101790 f s t) = (term96 _101783 _101790 f s t).
Proof. exact (MK_COMB (@lem4016045) (@lem4016044 _101783 _101790 f s t)). Qed.
Lemma lem4016047 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) : (term105 _101783 _101790 f s t) = (term97 _101783 _101790 f s t).
Proof. exact (TRANS (@lem4016046 _101783 _101790 f s t) (@lem4016041 _101783 _101790 f s t)). Qed.
Lemma lem4016048 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term106 _101783 _101790 f s) = (term107 _101783 _101790 f s).
Proof. exact (fun_ext (fun t : _101783 -> Prop => @lem4016047 _101783 _101790 f s t)). Qed.
Lemma lem4016049 {_101783 : Type'} : (@ex (_101783 -> Prop)) = (@ex (_101783 -> Prop)).
Proof. exact (eq_refl (@ex (_101783 -> Prop))). Qed.
Lemma lem4016050 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term103 _101783 _101790 f s) = (term108 _101783 _101790 f s).
Proof. exact (MK_COMB (@lem4016049 _101783) (@lem4016048 _101783 _101790 f s)). Qed.
Lemma lem4016051 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term102 _101783 _101790 f s) = (term108 _101783 _101790 f s).
Proof. exact (TRANS (@lem4016043 _101783 _101790 f s) (@lem4016050 _101783 _101790 f s)). Qed.
Lemma lem4016052 {_101790 : Type'} (P : type686 _101790) : (term100 _101790 P) = (term101 _101790 P).
Proof. exact (@lem18392 (_101790 -> Prop) P). Qed.
Lemma lem4016053 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term109 _101783 _101790 f) = (term110 _101783 _101790 f).
Proof. exact (@lem4016052 _101790 (term93 _101783 _101790 f)). Qed.
Lemma lem4016054 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term111 _101783 _101790 f s) = (term92 _101783 _101790 f s).
Proof. exact (eq_refl (term111 _101783 _101790 f s)). Qed.
Lemma lem4016055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4016056 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term112 _101783 _101790 f s) = (term102 _101783 _101790 f s).
Proof. exact (MK_COMB (@lem4016055) (@lem4016054 _101783 _101790 f s)). Qed.
Lemma lem4016057 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) : (term112 _101783 _101790 f s) = (term108 _101783 _101790 f s).
Proof. exact (TRANS (@lem4016056 _101783 _101790 f s) (@lem4016051 _101783 _101790 f s)). Qed.
Lemma lem4016058 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term113 _101783 _101790 f) = (term114 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101790 -> Prop => @lem4016057 _101783 _101790 f s)). Qed.
Lemma lem4016059 {_101790 : Type'} : (@ex (_101790 -> Prop)) = (@ex (_101790 -> Prop)).
Proof. exact (eq_refl (@ex (_101790 -> Prop))). Qed.
Lemma lem4016060 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term110 _101783 _101790 f) = (term115 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4016059 _101790) (@lem4016058 _101783 _101790 f)). Qed.
Lemma lem4016061 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term109 _101783 _101790 f) = (term115 _101783 _101790 f).
Proof. exact (TRANS (@lem4016053 _101783 _101790 f) (@lem4016060 _101783 _101790 f)). Qed.
Lemma lem4016062 {_101783 _101790 : Type'} (P : type572 _101783 _101790) : (term116 _101783 _101790 P) = (term117 _101783 _101790 P).
Proof. exact (@lem18392 (_101783 -> _101790) P). Qed.
Lemma lem4016063 {_101783 _101790 : Type'} : (term10 _101783 _101790) = (term118 _101783 _101790).
Proof. exact (@lem4016062 _101783 _101790 (term95 _101783 _101790)). Qed.
Lemma lem4016064 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term119 _101783 _101790 f) = (term94 _101783 _101790 f).
Proof. exact (eq_refl (term119 _101783 _101790 f)). Qed.
Lemma lem4016065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4016066 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term120 _101783 _101790 f) = (term109 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4016065) (@lem4016064 _101783 _101790 f)). Qed.
Lemma lem4016067 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term120 _101783 _101790 f) = (term115 _101783 _101790 f).
Proof. exact (TRANS (@lem4016066 _101783 _101790 f) (@lem4016061 _101783 _101790 f)). Qed.
Lemma lem4016068 {_101783 _101790 : Type'} : (term121 _101783 _101790) = (term122 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4016067 _101783 _101790 f)). Qed.
Lemma lem4016069 {_101783 _101790 : Type'} : (@ex (_101783 -> _101790)) = (@ex (_101783 -> _101790)).
Proof. exact (eq_refl (@ex (_101783 -> _101790))). Qed.
Lemma lem4016070 {_101783 _101790 : Type'} : (term118 _101783 _101790) = (term123 _101783 _101790).
Proof. exact (MK_COMB (@lem4016069 _101783 _101790) (@lem4016068 _101783 _101790)). Qed.
Lemma lem4016131 {_101783 _101790 : Type'} : (term10 _101783 _101790) = (term123 _101783 _101790).
Proof. exact (TRANS (@lem4016063 _101783 _101790) (@lem4016070 _101783 _101790)). Qed.
Lemma lem4016132 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : term123 _101783 _101790.
Proof. exact (EQ_MP (@lem4016131 _101783 _101790) (@lem4016015 _101783 _101790 h1)). Qed.
Lemma lem4016215 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term124 _101790 a b) = (term125 _101790 a b).
Proof. exact (@lem17045 (@SUBSET _101790 a b) (@FINITE _101790 b)). Qed.
Lemma lem4016216 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term126 _101790 a b) = (term126 _101790 a b).
Proof. exact (eq_refl (term126 _101790 a b)). Qed.
Lemma lem4016217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4016218 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term127 _101790 a b) = (term128 _101790 a b).
Proof. exact (MK_COMB (@lem4016217) (@lem4016215 _101790 a b)). Qed.
Lemma lem4016219 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term129 _101790 a b) = (term130 _101790 a b).
Proof. exact (MK_COMB (@lem4016218 _101790 a b) (@lem4016216 _101790 a b)). Qed.
Lemma lem4016220 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term86 _101790 a b) = (term129 _101790 a b).
Proof. exact (@lem17265 (term131 _101790 a b) (term126 _101790 a b)). Qed.
Lemma lem4016221 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term86 _101790 a b) = (term130 _101790 a b).
Proof. exact (TRANS (@lem4016220 _101790 a b) (@lem4016219 _101790 a b)). Qed.
Lemma lem4016222 {_101790 : Type'} (a : _101790 -> Prop) : (term87 _101790 a) = (term132 _101790 a).
Proof. exact (fun_ext (fun b : _101790 -> Prop => @lem4016221 _101790 a b)). Qed.
Lemma lem4016223 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4016224 {_101790 : Type'} (a : _101790 -> Prop) : (term88 _101790 a) = (term133 _101790 a).
Proof. exact (MK_COMB (@lem4016223 _101790) (@lem4016222 _101790 a)). Qed.
Lemma lem4016225 {_101790 : Type'} : (term89 _101790) = (term134 _101790).
Proof. exact (fun_ext (fun a : _101790 -> Prop => @lem4016224 _101790 a)). Qed.
Lemma lem4016226 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4016283 {_101790 : Type'} : (term16 _101790) = (term135 _101790).
Proof. exact (MK_COMB (@lem4016226 _101790) (@lem4016225 _101790)). Qed.
Lemma lem4016284 {_101790 : Type'} (h1 : term16 _101790) : term135 _101790.
Proof. exact (EQ_MP (@lem4016283 _101790) (@lem4016017 _101790 h1)). Qed.
Lemma lem4016443 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term78 _101783 _101790 f s) = (term136 _101783 _101790 f s).
Proof. exact (@lem17265 (@FINITE _101783 s) (term137 _101783 _101790 f s)). Qed.
Lemma lem4016444 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term79 _101783 _101790 f) = (term138 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4016443 _101783 _101790 f s)). Qed.
Lemma lem4016445 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4016446 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term80 _101783 _101790 f) = (term139 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4016445 _101783) (@lem4016444 _101783 _101790 f)). Qed.
Lemma lem4016447 {_101783 _101790 : Type'} : (term81 _101783 _101790) = (term140 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4016446 _101783 _101790 f)). Qed.
Lemma lem4016448 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4016505 {_101783 _101790 : Type'} : (term13 _101783 _101790) = (term141 _101783 _101790).
Proof. exact (MK_COMB (@lem4016448 _101783 _101790) (@lem4016447 _101783 _101790)). Qed.
Lemma lem4016506 {_101783 _101790 : Type'} (h1 : term13 _101783 _101790) : term141 _101783 _101790.
Proof. exact (EQ_MP (@lem4016505 _101783 _101790) (@lem4016020 _101783 _101790 h1)). Qed.
Lemma lem4016933 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term70 _101783 _101790 f s) = (term142 _101783 _101790 f s).
Proof. exact (@lem17265 (@FINITE _101783 s) (term143 _101783 _101790 f s)). Qed.
Lemma lem4016934 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term71 _101783 _101790 f) = (term144 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4016933 _101783 _101790 f s)). Qed.
Lemma lem4016935 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4016936 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term72 _101783 _101790 f) = (term145 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4016935 _101783) (@lem4016934 _101783 _101790 f)). Qed.
Lemma lem4016937 {_101783 _101790 : Type'} : (term73 _101783 _101790) = (term146 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4016936 _101783 _101790 f)). Qed.
Lemma lem4016938 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4016995 {_101783 _101790 : Type'} : (term11 _101783 _101790) = (term147 _101783 _101790).
Proof. exact (MK_COMB (@lem4016938 _101783 _101790) (@lem4016937 _101783 _101790)). Qed.
Lemma lem4016996 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) : term147 _101783 _101790.
Proof. exact (EQ_MP (@lem4016995 _101783 _101790) (@lem4016027 _101783 _101790 h1)). Qed.
Lemma lem4017143 (m : nat) (n : nat) (p : nat) : (term148 m n p) = (term149 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem4017144 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem4017145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4017146 (m : nat) (n : nat) (p : nat) : (term150 m n p) = (term151 m n p).
Proof. exact (MK_COMB (@lem4017145) (@lem4017143 m n p)). Qed.
Lemma lem4017147 (n : nat) (m : nat) (p : nat) : (term152 n m p) = (term153 n m p).
Proof. exact (MK_COMB (@lem4017146 m n p) (@lem4017144 m p)). Qed.
Lemma lem4017148 (n : nat) (m : nat) (p : nat) : (term60 n m p) = (term152 n m p).
Proof. exact (@lem17265 (term154 m n p) (Peano.le m p)). Qed.
Lemma lem4017149 (n : nat) (m : nat) (p : nat) : (term60 n m p) = (term153 n m p).
Proof. exact (TRANS (@lem4017148 n m p) (@lem4017147 n m p)). Qed.
Lemma lem4017150 (n : nat) (m : nat) : (term61 n m) = (term155 n m).
Proof. exact (fun_ext (fun p : nat => @lem4017149 n m p)). Qed.
Lemma lem4017151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017152 (n : nat) (m : nat) : (term62 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem4017151) (@lem4017150 n m)). Qed.
Lemma lem4017153 (m : nat) : (term63 m) = (term157 m).
Proof. exact (fun_ext (fun n : nat => @lem4017152 n m)). Qed.
Lemma lem4017154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017155 (m : nat) : (term64 m) = (term158 m).
Proof. exact (MK_COMB (@lem4017154) (@lem4017153 m)). Qed.
Lemma lem4017156 : term65 = term159.
Proof. exact (fun_ext (fun m : nat => @lem4017155 m)). Qed.
Lemma lem4017157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017218 : term23 = term160.
Proof. exact (MK_COMB (@lem4017157) (@lem4017156)). Qed.
Lemma lem4017219 (h1 : term23) : term160.
Proof. exact (EQ_MP (@lem4017218) (@lem4016030 h1)). Qed.
Lemma lem4017220 {_101783 _101790 : Type'} (f : _101783 -> _101790) (h1 : term115 _101783 _101790 f) : term115 _101783 _101790 f.
Proof. exact (h1). Qed.
Lemma lem4017221 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (h1 : term108 _101783 _101790 f s) : term108 _101783 _101790 f s.
Proof. exact (h1). Qed.
Lemma lem4017283 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term130 _101790 a b) = (term130 _101790 a b).
Proof. exact (eq_refl (term130 _101790 a b)). Qed.
Lemma lem4017284 {_101790 : Type'} (a : _101790 -> Prop) : (term132 _101790 a) = (term132 _101790 a).
Proof. exact (fun_ext (fun b : _101790 -> Prop => @lem4017283 _101790 a b)). Qed.
Lemma lem4017285 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4017286 {_101790 : Type'} (a : _101790 -> Prop) : (term133 _101790 a) = (term133 _101790 a).
Proof. exact (MK_COMB (@lem4017285 _101790) (@lem4017284 _101790 a)). Qed.
Lemma lem4017287 {_101790 : Type'} : (term134 _101790) = (term134 _101790).
Proof. exact (fun_ext (fun a : _101790 -> Prop => @lem4017286 _101790 a)). Qed.
Lemma lem4017288 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4017289 {_101790 : Type'} : (term135 _101790) = (term135 _101790).
Proof. exact (MK_COMB (@lem4017288 _101790) (@lem4017287 _101790)). Qed.
Lemma lem4017290 {_101790 : Type'} (h1 : term16 _101790) : term135 _101790.
Proof. exact (EQ_MP (@lem4017289 _101790) (@lem4016284 _101790 h1)). Qed.
Lemma lem4017379 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term136 _101783 _101790 f s) = (term136 _101783 _101790 f s).
Proof. exact (eq_refl (term136 _101783 _101790 f s)). Qed.
Lemma lem4017380 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term138 _101783 _101790 f) = (term138 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4017379 _101783 _101790 f s)). Qed.
Lemma lem4017381 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4017382 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term139 _101783 _101790 f) = (term139 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4017381 _101783) (@lem4017380 _101783 _101790 f)). Qed.
Lemma lem4017383 {_101783 _101790 : Type'} : (term140 _101783 _101790) = (term140 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4017382 _101783 _101790 f)). Qed.
Lemma lem4017384 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4017385 {_101783 _101790 : Type'} : (term141 _101783 _101790) = (term141 _101783 _101790).
Proof. exact (MK_COMB (@lem4017384 _101783 _101790) (@lem4017383 _101783 _101790)). Qed.
Lemma lem4017386 {_101783 _101790 : Type'} (h1 : term13 _101783 _101790) : term141 _101783 _101790.
Proof. exact (EQ_MP (@lem4017385 _101783 _101790) (@lem4016506 _101783 _101790 h1)). Qed.
Lemma lem4017569 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term142 _101783 _101790 f s) = (term142 _101783 _101790 f s).
Proof. exact (eq_refl (term142 _101783 _101790 f s)). Qed.
Lemma lem4017570 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term144 _101783 _101790 f) = (term144 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4017569 _101783 _101790 f s)). Qed.
Lemma lem4017571 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4017572 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term145 _101783 _101790 f) = (term145 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4017571 _101783) (@lem4017570 _101783 _101790 f)). Qed.
Lemma lem4017573 {_101783 _101790 : Type'} : (term146 _101783 _101790) = (term146 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4017572 _101783 _101790 f)). Qed.
Lemma lem4017574 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4017575 {_101783 _101790 : Type'} : (term147 _101783 _101790) = (term147 _101783 _101790).
Proof. exact (MK_COMB (@lem4017574 _101783 _101790) (@lem4017573 _101783 _101790)). Qed.
Lemma lem4017576 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) : term147 _101783 _101790.
Proof. exact (EQ_MP (@lem4017575 _101783 _101790) (@lem4016996 _101783 _101790 h1)). Qed.
Lemma lem4017645 (n : nat) (m : nat) (p : nat) : (term153 n m p) = (term153 n m p).
Proof. exact (eq_refl (term153 n m p)). Qed.
Lemma lem4017646 (n : nat) (m : nat) : (term155 n m) = (term155 n m).
Proof. exact (fun_ext (fun p : nat => @lem4017645 n m p)). Qed.
Lemma lem4017647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017648 (n : nat) (m : nat) : (term156 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem4017647) (@lem4017646 n m)). Qed.
Lemma lem4017649 (m : nat) : (term157 m) = (term157 m).
Proof. exact (fun_ext (fun n : nat => @lem4017648 n m)). Qed.
Lemma lem4017650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017651 (m : nat) : (term158 m) = (term158 m).
Proof. exact (MK_COMB (@lem4017650) (@lem4017649 m)). Qed.
Lemma lem4017652 : term159 = term159.
Proof. exact (fun_ext (fun m : nat => @lem4017651 m)). Qed.
Lemma lem4017653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017654 : term160 = term160.
Proof. exact (MK_COMB (@lem4017653) (@lem4017652)). Qed.
Lemma lem4017655 (h1 : term23) : term160.
Proof. exact (EQ_MP (@lem4017654) (@lem4017219 h1)). Qed.
Lemma lem4017685 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term97 _101783 _101790 f s t.
Proof. exact (h1). Qed.
Lemma lem4017687 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term98 _101783 _101790 s f t.
Proof. exact (proj1 (@lem4017685 _101783 _101790 f s t h1)). Qed.
Lemma lem4017725 {_101790 : Type'} (a : _101790 -> Prop) (b : _101790 -> Prop) : (term130 _101790 a b) = (term130 _101790 a b).
Proof. exact (eq_refl (term130 _101790 a b)). Qed.
Lemma lem4017726 {_101790 : Type'} (a : _101790 -> Prop) : (term132 _101790 a) = (term132 _101790 a).
Proof. exact (fun_ext (fun b : _101790 -> Prop => @lem4017725 _101790 a b)). Qed.
Lemma lem4017727 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4017728 {_101790 : Type'} (a : _101790 -> Prop) : (term133 _101790 a) = (term133 _101790 a).
Proof. exact (MK_COMB (@lem4017727 _101790) (@lem4017726 _101790 a)). Qed.
Lemma lem4017729 {_101790 : Type'} : (term134 _101790) = (term134 _101790).
Proof. exact (fun_ext (fun a : _101790 -> Prop => @lem4017728 _101790 a)). Qed.
Lemma lem4017730 {_101790 : Type'} : (@all (_101790 -> Prop)) = (@all (_101790 -> Prop)).
Proof. exact (eq_refl (@all (_101790 -> Prop))). Qed.
Lemma lem4017732 {_101790 : Type'} : (term135 _101790) = (term135 _101790).
Proof. exact (MK_COMB (@lem4017730 _101790) (@lem4017729 _101790)). Qed.
Lemma lem4017733 {_101790 : Type'} (h1 : term16 _101790) : term135 _101790.
Proof. exact (EQ_MP (@lem4017732 _101790) (@lem4017290 _101790 h1)). Qed.
Lemma lem4017785 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term136 _101783 _101790 f s) = (term136 _101783 _101790 f s).
Proof. exact (eq_refl (term136 _101783 _101790 f s)). Qed.
Lemma lem4017786 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term138 _101783 _101790 f) = (term138 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4017785 _101783 _101790 f s)). Qed.
Lemma lem4017787 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4017788 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term139 _101783 _101790 f) = (term139 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4017787 _101783) (@lem4017786 _101783 _101790 f)). Qed.
Lemma lem4017789 {_101783 _101790 : Type'} : (term140 _101783 _101790) = (term140 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4017788 _101783 _101790 f)). Qed.
Lemma lem4017790 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4017792 {_101783 _101790 : Type'} : (term141 _101783 _101790) = (term141 _101783 _101790).
Proof. exact (MK_COMB (@lem4017790 _101783 _101790) (@lem4017789 _101783 _101790)). Qed.
Lemma lem4017793 {_101783 _101790 : Type'} (h1 : term13 _101783 _101790) : term141 _101783 _101790.
Proof. exact (EQ_MP (@lem4017792 _101783 _101790) (@lem4017386 _101783 _101790 h1)). Qed.
Lemma lem4017897 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101783 -> Prop) : (term142 _101783 _101790 f s) = (term142 _101783 _101790 f s).
Proof. exact (eq_refl (term142 _101783 _101790 f s)). Qed.
Lemma lem4017898 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term144 _101783 _101790 f) = (term144 _101783 _101790 f).
Proof. exact (fun_ext (fun s : _101783 -> Prop => @lem4017897 _101783 _101790 f s)). Qed.
Lemma lem4017899 {_101783 : Type'} : (@all (_101783 -> Prop)) = (@all (_101783 -> Prop)).
Proof. exact (eq_refl (@all (_101783 -> Prop))). Qed.
Lemma lem4017900 {_101783 _101790 : Type'} (f : _101783 -> _101790) : (term145 _101783 _101790 f) = (term145 _101783 _101790 f).
Proof. exact (MK_COMB (@lem4017899 _101783) (@lem4017898 _101783 _101790 f)). Qed.
Lemma lem4017901 {_101783 _101790 : Type'} : (term146 _101783 _101790) = (term146 _101783 _101790).
Proof. exact (fun_ext (fun f : _101783 -> _101790 => @lem4017900 _101783 _101790 f)). Qed.
Lemma lem4017902 {_101783 _101790 : Type'} : (@all (_101783 -> _101790)) = (@all (_101783 -> _101790)).
Proof. exact (eq_refl (@all (_101783 -> _101790))). Qed.
Lemma lem4017904 {_101783 _101790 : Type'} : (term147 _101783 _101790) = (term147 _101783 _101790).
Proof. exact (MK_COMB (@lem4017902 _101783 _101790) (@lem4017901 _101783 _101790)). Qed.
Lemma lem4017905 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) : term147 _101783 _101790.
Proof. exact (EQ_MP (@lem4017904 _101783 _101790) (@lem4017576 _101783 _101790 h1)). Qed.
Lemma lem4017951 (n : nat) (m : nat) (p : nat) : (term153 n m p) = (term153 n m p).
Proof. exact (eq_refl (term153 n m p)). Qed.
Lemma lem4017952 (n : nat) (m : nat) : (term155 n m) = (term155 n m).
Proof. exact (fun_ext (fun p : nat => @lem4017951 n m p)). Qed.
Lemma lem4017953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017954 (n : nat) (m : nat) : (term156 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem4017953) (@lem4017952 n m)). Qed.
Lemma lem4017955 (m : nat) : (term157 m) = (term157 m).
Proof. exact (fun_ext (fun n : nat => @lem4017954 n m)). Qed.
Lemma lem4017956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017957 (m : nat) : (term158 m) = (term158 m).
Proof. exact (MK_COMB (@lem4017956) (@lem4017955 m)). Qed.
Lemma lem4017958 : term159 = term159.
Proof. exact (fun_ext (fun m : nat => @lem4017957 m)). Qed.
Lemma lem4017959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4017961 : term160 = term160.
Proof. exact (MK_COMB (@lem4017959) (@lem4017958)). Qed.
Lemma lem4017962 (h1 : term23) : term160.
Proof. exact (EQ_MP (@lem4017961) (@lem4017655 h1)). Qed.
Lemma lem4017981 {_101790 : Type'} (_46393 : _101790 -> Prop) (h1 : term16 _101790) : term161 _101790 _46393.
Proof. exact (@lem4017733 _101790 h1 _46393). Qed.
Lemma lem4017982 {_101790 : Type'} (_46393 : _101790 -> Prop) : (term161 _101790 _46393) = (term133 _101790 _46393).
Proof. exact (eq_refl (term161 _101790 _46393)). Qed.
Lemma lem4017983 {_101790 : Type'} (_46393 : _101790 -> Prop) (h1 : term16 _101790) : term133 _101790 _46393.
Proof. exact (EQ_MP (@lem4017982 _101790 _46393) (@lem4017981 _101790 _46393 h1)). Qed.
Lemma lem4017984 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term162 _101790 _46393 _46394.
Proof. exact (@lem4017983 _101790 _46393 h1 _46394). Qed.
Lemma lem4017985 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term162 _101790 _46393 _46394) = (term130 _101790 _46393 _46394).
Proof. exact (eq_refl (term162 _101790 _46393 _46394)). Qed.
Lemma lem4017986 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term130 _101790 _46393 _46394.
Proof. exact (EQ_MP (@lem4017985 _101790 _46393 _46394) (@lem4017984 _101790 _46393 _46394 h1)). Qed.
Lemma lem4017999 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (h1 : term13 _101783 _101790) : term163 _101783 _101790 _46399.
Proof. exact (@lem4017793 _101783 _101790 h1 _46399). Qed.
Lemma lem4018000 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) : (term163 _101783 _101790 _46399) = (term139 _101783 _101790 _46399).
Proof. exact (eq_refl (term163 _101783 _101790 _46399)). Qed.
Lemma lem4018001 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (h1 : term13 _101783 _101790) : term139 _101783 _101790 _46399.
Proof. exact (EQ_MP (@lem4018000 _101783 _101790 _46399) (@lem4017999 _101783 _101790 _46399 h1)). Qed.
Lemma lem4018002 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) (h1 : term13 _101783 _101790) : term164 _101783 _101790 _46399 _46400.
Proof. exact (@lem4018001 _101783 _101790 _46399 h1 _46400). Qed.
Lemma lem4018003 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term164 _101783 _101790 _46399 _46400) = (term136 _101783 _101790 _46399 _46400).
Proof. exact (eq_refl (term164 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018041 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (h1 : term11 _101783 _101790) : term165 _101783 _101790 _46413.
Proof. exact (@lem4017905 _101783 _101790 h1 _46413). Qed.
Lemma lem4018042 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) : (term165 _101783 _101790 _46413) = (term145 _101783 _101790 _46413).
Proof. exact (eq_refl (term165 _101783 _101790 _46413)). Qed.
Lemma lem4018043 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (h1 : term11 _101783 _101790) : term145 _101783 _101790 _46413.
Proof. exact (EQ_MP (@lem4018042 _101783 _101790 _46413) (@lem4018041 _101783 _101790 _46413 h1)). Qed.
Lemma lem4018044 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) (h1 : term11 _101783 _101790) : term166 _101783 _101790 _46413 _46414.
Proof. exact (@lem4018043 _101783 _101790 _46413 h1 _46414). Qed.
Lemma lem4018045 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term166 _101783 _101790 _46413 _46414) = (term142 _101783 _101790 _46413 _46414).
Proof. exact (eq_refl (term166 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018059 (_46419 : nat) (h1 : term23) : term167 _46419.
Proof. exact (@lem4017962 h1 _46419). Qed.
Lemma lem4018060 (_46419 : nat) : (term167 _46419) = (term158 _46419).
Proof. exact (eq_refl (term167 _46419)). Qed.
Lemma lem4018061 (_46419 : nat) (h1 : term23) : term158 _46419.
Proof. exact (EQ_MP (@lem4018060 _46419) (@lem4018059 _46419 h1)). Qed.
Lemma lem4018062 (_46419 : nat) (_46420 : nat) (h1 : term23) : term168 _46419 _46420.
Proof. exact (@lem4018061 _46419 h1 _46420). Qed.
Lemma lem4018063 (_46420 : nat) (_46419 : nat) : (term168 _46419 _46420) = (term156 _46420 _46419).
Proof. exact (eq_refl (term168 _46419 _46420)). Qed.
Lemma lem4018064 (_46420 : nat) (_46419 : nat) (h1 : term23) : term156 _46420 _46419.
Proof. exact (EQ_MP (@lem4018063 _46420 _46419) (@lem4018062 _46419 _46420 h1)). Qed.
Lemma lem4018065 (_46420 : nat) (_46419 : nat) (_46421 : nat) (h1 : term23) : term169 _46420 _46419 _46421.
Proof. exact (@lem4018064 _46420 _46419 h1 _46421). Qed.
Lemma lem4018066 (_46420 : nat) (_46419 : nat) (_46421 : nat) : (term169 _46420 _46419 _46421) = (term153 _46420 _46419 _46421).
Proof. exact (eq_refl (term169 _46420 _46419 _46421)). Qed.
Lemma lem4018067 (_46420 : nat) (_46419 : nat) (_46421 : nat) (h1 : term23) : term153 _46420 _46419 _46421.
Proof. exact (EQ_MP (@lem4018066 _46420 _46419 _46421) (@lem4018065 _46420 _46419 _46421 h1)). Qed.
Lemma lem4018090 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term130 _101790 _46393 _46394) = (term170 _101790 _46393 _46394).
Proof. exact (@lem4015156 (term171 _101790 _46393 _46394) (term172 _101790 _46394) (term126 _101790 _46393 _46394)). Qed.
Lemma lem4018091 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term170 _101790 _46393 _46394.
Proof. exact (EQ_MP (@lem4018090 _101790 _46393 _46394) (@lem4017986 _101790 _46393 _46394 h1)). Qed.
Lemma lem4018121 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) (h1 : term13 _101783 _101790) : term136 _101783 _101790 _46399 _46400.
Proof. exact (EQ_MP (@lem4018003 _101783 _101790 _46399 _46400) (@lem4018002 _101783 _101790 _46399 _46400 h1)). Qed.
Lemma lem4018163 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) (h1 : term11 _101783 _101790) : term142 _101783 _101790 _46413 _46414.
Proof. exact (EQ_MP (@lem4018045 _101783 _101790 _46413 _46414) (@lem4018044 _101783 _101790 _46413 _46414 h1)). Qed.
Lemma lem4018186 (_46420 : nat) (_46419 : nat) (_46421 : nat) : (term153 _46420 _46419 _46421) = (term173 _46420 _46419 _46421).
Proof. exact (@lem4015156 (term174 _46419 _46420) (term174 _46420 _46421) (Peano.le _46419 _46421)). Qed.
Lemma lem4018187 (_46420 : nat) (_46419 : nat) (_46421 : nat) (h1 : term23) : term173 _46420 _46419 _46421.
Proof. exact (EQ_MP (@lem4018186 _46420 _46419 _46421) (@lem4018067 _46420 _46419 _46421 h1)). Qed.
Lemma lem4018189 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term175 _101783 _101790 s t.
Proof. exact (proj2 (@lem4017685 _101783 _101790 f s t h1)). Qed.
Lemma lem4018195 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term176 _101783 _101790 s f t.
Proof. exact (proj2 (@lem4017687 _101783 _101790 f s t h1)). Qed.
Lemma lem4018196 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term177 _101783 _101790 s f t.
Proof. exact (fun h0 : term178 _101783 _101790 s f t => @lem4018195 _101783 _101790 f s t h1). Qed.
Lemma lem4018198 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018199 {_101783 _101790 : Type'} (s : _101790 -> Prop) (f : _101783 -> _101790) (t : _101783 -> Prop) : (term177 _101783 _101790 s f t) = (term176 _101783 _101790 s f t).
Proof. exact (@lem4018198 (term176 _101783 _101790 s f t)). Qed.
Lemma lem4018200 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term176 _101783 _101790 s f t.
Proof. exact (EQ_MP (@lem4018199 _101783 _101790 s f t) (@lem4018196 _101783 _101790 f s t h1)). Qed.
Lemma lem4018202 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : @FINITE _101783 t.
Proof. exact (proj1 (@lem4017687 _101783 _101790 f s t h1)). Qed.
Lemma lem4018203 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term180 _101783 t.
Proof. exact (fun h0 : term172 _101783 t => @lem4018202 _101783 _101790 f s t h1). Qed.
Lemma lem4018205 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018206 {_101783 : Type'} (t : _101783 -> Prop) : (term180 _101783 t) = (@FINITE _101783 t).
Proof. exact (@lem4018205 (@FINITE _101783 t)). Qed.
Lemma lem4018207 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : @FINITE _101783 t.
Proof. exact (EQ_MP (@lem4018206 _101783 t) (@lem4018203 _101783 _101790 f s t h1)). Qed.
Lemma lem4018213 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4018214 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term142 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414).
Proof. exact (@lem4018213 (term143 _101783 _101790 _46413 _46414) (term172 _101783 _46414)). Qed.
Lemma lem4018220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018221 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term182 _101783 _101790 _46413 _46414) = (term183 _101783 _101790 _46413 _46414).
Proof. exact (MK_COMB (@lem4018220) (@lem4018214 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018227 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term181 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414).
Proof. exact (eq_refl (term181 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018228 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : ((term142 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414)) = ((term181 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414)).
Proof. exact (MK_COMB (@lem4018221 _101783 _101790 _46413 _46414) (@lem4018227 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018230 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4018231 (x : Prop) : (x = x) = True.
Proof. exact (@lem4018230 Prop x). Qed.
Lemma lem4018232 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : ((term181 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414)) = True.
Proof. exact (@lem4018231 (term181 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018233 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : ((term142 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414)) = True.
Proof. exact (TRANS (@lem4018228 _101783 _101790 _46413 _46414) (@lem4018232 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018234 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : True = ((term142 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414)).
Proof. exact (SYM (@lem4018233 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018235 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term142 _101783 _101790 _46413 _46414) = (term181 _101783 _101790 _46413 _46414).
Proof. exact (EQ_MP (@lem4018234 _101783 _101790 _46413 _46414) (@lem0)). Qed.
Lemma lem4018236 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) (h1 : term11 _101783 _101790) : term181 _101783 _101790 _46413 _46414.
Proof. exact (EQ_MP (@lem4018235 _101783 _101790 _46413 _46414) (@lem4018163 _101783 _101790 _46413 _46414 h1)). Qed.
Lemma lem4018238 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4018239 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term181 _101783 _101790 _46413 _46414) = (term185 _101783 _101790 _46413 _46414).
Proof. exact (@lem4018238 (term172 _101783 _46414) (term143 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018241 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018242 {_101783 : Type'} (_46414 : _101783 -> Prop) : (term187 _101783 _46414) = (@FINITE _101783 _46414).
Proof. exact (@lem4018241 (@FINITE _101783 _46414)). Qed.
Lemma lem4018243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018244 {_101783 : Type'} (_46414 : _101783 -> Prop) : (term188 _101783 _46414) = (term189 _101783 _46414).
Proof. exact (MK_COMB (@lem4018243) (@lem4018242 _101783 _46414)). Qed.
Lemma lem4018245 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term143 _101783 _101790 _46413 _46414) = (term143 _101783 _101790 _46413 _46414).
Proof. exact (eq_refl (term143 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018246 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term185 _101783 _101790 _46413 _46414) = (term70 _101783 _101790 _46413 _46414).
Proof. exact (MK_COMB (@lem4018244 _101783 _46414) (@lem4018245 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018247 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) : (term181 _101783 _101790 _46413 _46414) = (term70 _101783 _101790 _46413 _46414).
Proof. exact (TRANS (@lem4018239 _101783 _101790 _46413 _46414) (@lem4018246 _101783 _101790 _46413 _46414)). Qed.
Lemma lem4018250 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) (h1 : term11 _101783 _101790) : term70 _101783 _101790 _46413 _46414.
Proof. exact (EQ_MP (@lem4018247 _101783 _101790 _46413 _46414) (@lem4018236 _101783 _101790 _46413 _46414 h1)). Qed.
Lemma lem4018251 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (_46414 : _101783 -> Prop) (h1 : term11 _101783 _101790) : term70 _101783 _101790 _46413 _46414.
Proof. exact (@lem4018250 _101783 _101790 _46413 _46414 h1). Qed.
Lemma lem4018252 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) : term70 _101783 _101790 _46413 t.
Proof. exact (@lem4018251 _101783 _101790 _46413 t h1). Qed.
Lemma lem4018255 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term143 _101783 _101790 _46413 t.
Proof. exact (@lem4018252 _101783 _101790 _46413 t h1 (@lem4018207 _101783 _101790 f s t h2)). Qed.
Lemma lem4018256 {_101783 _101790 : Type'} (_46413 : _101783 -> _101790) (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term143 _101783 _101790 _46413 t.
Proof. exact (@lem4018255 _101783 _101790 _46413 f s t h1 h2). Qed.
Lemma lem4018257 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term143 _101783 _101790 f t.
Proof. exact (@lem4018256 _101783 _101790 f f s t h1 h2). Qed.
Lemma lem4018258 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term190 _101783 _101790 f t.
Proof. exact (fun h0 : term191 _101783 _101790 f t => @lem4018257 _101783 _101790 f s t h1 h2). Qed.
Lemma lem4018260 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018261 {_101783 _101790 : Type'} (f : _101783 -> _101790) (t : _101783 -> Prop) : (term190 _101783 _101790 f t) = (term143 _101783 _101790 f t).
Proof. exact (@lem4018260 (term143 _101783 _101790 f t)). Qed.
Lemma lem4018262 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term143 _101783 _101790 f t.
Proof. exact (EQ_MP (@lem4018261 _101783 _101790 f t) (@lem4018258 _101783 _101790 f s t h1 h2)). Qed.
Lemma lem4018268 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4018269 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term170 _101790 _46393 _46394) = (term192 _101790 _46393 _46394).
Proof. exact (@lem4018268 (term172 _101790 _46394) (term171 _101790 _46393 _46394) (term126 _101790 _46393 _46394)). Qed.
Lemma lem4018283 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4018284 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term193 _101790 _46393 _46394) = (term194 _101790 _46393 _46394).
Proof. exact (@lem4018283 (term126 _101790 _46393 _46394) (term171 _101790 _46393 _46394)). Qed.
Lemma lem4018290 {_101790 : Type'} (_46394 : _101790 -> Prop) : (term195 _101790 _46394) = (term195 _101790 _46394).
Proof. exact (eq_refl (term195 _101790 _46394)). Qed.
Lemma lem4018291 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term192 _101790 _46393 _46394) = (term196 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018290 _101790 _46394) (@lem4018284 _101790 _46393 _46394)). Qed.
Lemma lem4018295 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4018296 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term196 _101790 _46393 _46394) = (term197 _101790 _46393 _46394).
Proof. exact (@lem4018295 (term126 _101790 _46393 _46394) (term172 _101790 _46394) (term171 _101790 _46393 _46394)). Qed.
Lemma lem4018312 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term192 _101790 _46393 _46394) = (term197 _101790 _46393 _46394).
Proof. exact (TRANS (@lem4018291 _101790 _46393 _46394) (@lem4018296 _101790 _46393 _46394)). Qed.
Lemma lem4018313 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term170 _101790 _46393 _46394) = (term197 _101790 _46393 _46394).
Proof. exact (TRANS (@lem4018269 _101790 _46393 _46394) (@lem4018312 _101790 _46393 _46394)). Qed.
Lemma lem4018314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018315 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term198 _101790 _46393 _46394) = (term199 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018314) (@lem4018313 _101790 _46393 _46394)). Qed.
Lemma lem4018329 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4018330 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term125 _101790 _46393 _46394) = (term200 _101790 _46393 _46394).
Proof. exact (@lem4018329 (term172 _101790 _46394) (term171 _101790 _46393 _46394)). Qed.
Lemma lem4018336 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term201 _101790 _46393 _46394) = (term201 _101790 _46393 _46394).
Proof. exact (eq_refl (term201 _101790 _46393 _46394)). Qed.
Lemma lem4018337 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term202 _101790 _46393 _46394) = (term197 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018336 _101790 _46393 _46394) (@lem4018330 _101790 _46393 _46394)). Qed.
Lemma lem4018348 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : ((term170 _101790 _46393 _46394) = (term202 _101790 _46393 _46394)) = ((term197 _101790 _46393 _46394) = (term197 _101790 _46393 _46394)).
Proof. exact (MK_COMB (@lem4018315 _101790 _46393 _46394) (@lem4018337 _101790 _46393 _46394)). Qed.
Lemma lem4018350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4018351 (x : Prop) : (x = x) = True.
Proof. exact (@lem4018350 Prop x). Qed.
Lemma lem4018352 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : ((term197 _101790 _46393 _46394) = (term197 _101790 _46393 _46394)) = True.
Proof. exact (@lem4018351 (term197 _101790 _46393 _46394)). Qed.
Lemma lem4018353 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : ((term170 _101790 _46393 _46394) = (term202 _101790 _46393 _46394)) = True.
Proof. exact (TRANS (@lem4018348 _101790 _46393 _46394) (@lem4018352 _101790 _46393 _46394)). Qed.
Lemma lem4018354 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : True = ((term170 _101790 _46393 _46394) = (term202 _101790 _46393 _46394)).
Proof. exact (SYM (@lem4018353 _101790 _46393 _46394)). Qed.
Lemma lem4018355 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term170 _101790 _46393 _46394) = (term202 _101790 _46393 _46394).
Proof. exact (EQ_MP (@lem4018354 _101790 _46393 _46394) (@lem0)). Qed.
Lemma lem4018356 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term202 _101790 _46393 _46394.
Proof. exact (EQ_MP (@lem4018355 _101790 _46393 _46394) (@lem4018091 _101790 _46393 _46394 h1)). Qed.
Lemma lem4018358 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4018359 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term202 _101790 _46393 _46394) = (term203 _101790 _46393 _46394).
Proof. exact (@lem4018358 (term125 _101790 _46393 _46394) (term126 _101790 _46393 _46394)). Qed.
Lemma lem4018361 (a : Prop) (b : Prop) : (term204 a b) = (term205 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4018362 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term206 _101790 _46393 _46394) = (term207 _101790 _46393 _46394).
Proof. exact (@lem4018361 (term171 _101790 _46393 _46394) (term172 _101790 _46394)). Qed.
Lemma lem4018364 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018365 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term208 _101790 _46393 _46394) = (@SUBSET _101790 _46393 _46394).
Proof. exact (@lem4018364 (@SUBSET _101790 _46393 _46394)). Qed.
Lemma lem4018366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018367 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term209 _101790 _46393 _46394) = (term210 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018366) (@lem4018365 _101790 _46393 _46394)). Qed.
Lemma lem4018369 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018370 {_101790 : Type'} (_46394 : _101790 -> Prop) : (term187 _101790 _46394) = (@FINITE _101790 _46394).
Proof. exact (@lem4018369 (@FINITE _101790 _46394)). Qed.
Lemma lem4018371 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term207 _101790 _46393 _46394) = (term131 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018367 _101790 _46393 _46394) (@lem4018370 _101790 _46394)). Qed.
Lemma lem4018372 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term206 _101790 _46393 _46394) = (term131 _101790 _46393 _46394).
Proof. exact (TRANS (@lem4018362 _101790 _46393 _46394) (@lem4018371 _101790 _46393 _46394)). Qed.
Lemma lem4018373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018374 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term211 _101790 _46393 _46394) = (term212 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018373) (@lem4018372 _101790 _46393 _46394)). Qed.
Lemma lem4018375 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term126 _101790 _46393 _46394) = (term126 _101790 _46393 _46394).
Proof. exact (eq_refl (term126 _101790 _46393 _46394)). Qed.
Lemma lem4018376 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term203 _101790 _46393 _46394) = (term86 _101790 _46393 _46394).
Proof. exact (MK_COMB (@lem4018374 _101790 _46393 _46394) (@lem4018375 _101790 _46393 _46394)). Qed.
Lemma lem4018377 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) : (term202 _101790 _46393 _46394) = (term86 _101790 _46393 _46394).
Proof. exact (TRANS (@lem4018359 _101790 _46393 _46394) (@lem4018376 _101790 _46393 _46394)). Qed.
Lemma lem4018379 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term213 _101783 _101790 s f t.
Proof. exact (conj (@lem4018200 _101783 _101790 f s t h2) (@lem4018262 _101783 _101790 f s t h1 h2)). Qed.
Lemma lem4018381 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term86 _101790 _46393 _46394.
Proof. exact (EQ_MP (@lem4018377 _101790 _46393 _46394) (@lem4018356 _101790 _46393 _46394 h1)). Qed.
Lemma lem4018382 {_101790 : Type'} (_46393 : _101790 -> Prop) (_46394 : _101790 -> Prop) (h1 : term16 _101790) : term86 _101790 _46393 _46394.
Proof. exact (@lem4018381 _101790 _46393 _46394 h1). Qed.
Lemma lem4018383 {_101783 _101790 : Type'} (s : _101790 -> Prop) (f : _101783 -> _101790) (t : _101783 -> Prop) (h1 : term16 _101790) : term214 _101783 _101790 s f t.
Proof. exact (@lem4018382 _101790 s (@IMAGE _101783 _101790 f t) h1). Qed.
Lemma lem4018386 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term16 _101790) (h3 : term97 _101783 _101790 f s t) : term215 _101783 _101790 s f t.
Proof. exact (@lem4018383 _101783 _101790 s f t h2 (@lem4018379 _101783 _101790 f s t h1 h3)). Qed.
Lemma lem4018387 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term16 _101790) (h3 : term97 _101783 _101790 f s t) : term216 _101783 _101790 s f t.
Proof. exact (fun h0 : term217 _101783 _101790 s f t => @lem4018386 _101783 _101790 f s t h1 h2 h3). Qed.
Lemma lem4018389 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018390 {_101783 _101790 : Type'} (s : _101790 -> Prop) (f : _101783 -> _101790) (t : _101783 -> Prop) : (term216 _101783 _101790 s f t) = (term215 _101783 _101790 s f t).
Proof. exact (@lem4018389 (term215 _101783 _101790 s f t)). Qed.
Lemma lem4018391 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term16 _101790) (h3 : term97 _101783 _101790 f s t) : term215 _101783 _101790 s f t.
Proof. exact (EQ_MP (@lem4018390 _101783 _101790 s f t) (@lem4018387 _101783 _101790 f s t h1 h2 h3)). Qed.
Lemma lem4018393 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : @FINITE _101783 t.
Proof. exact (proj1 (@lem4017687 _101783 _101790 f s t h1)). Qed.
Lemma lem4018394 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term180 _101783 t.
Proof. exact (fun h0 : term172 _101783 t => @lem4018393 _101783 _101790 f s t h1). Qed.
Lemma lem4018396 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018397 {_101783 : Type'} (t : _101783 -> Prop) : (term180 _101783 t) = (@FINITE _101783 t).
Proof. exact (@lem4018396 (@FINITE _101783 t)). Qed.
Lemma lem4018398 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : @FINITE _101783 t.
Proof. exact (EQ_MP (@lem4018397 _101783 t) (@lem4018394 _101783 _101790 f s t h1)). Qed.
Lemma lem4018404 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4018405 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term136 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400).
Proof. exact (@lem4018404 (term137 _101783 _101790 _46399 _46400) (term172 _101783 _46400)). Qed.
Lemma lem4018411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018412 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term219 _101783 _101790 _46399 _46400) = (term220 _101783 _101790 _46399 _46400).
Proof. exact (MK_COMB (@lem4018411) (@lem4018405 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018418 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term218 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400).
Proof. exact (eq_refl (term218 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018419 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : ((term136 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400)) = ((term218 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400)).
Proof. exact (MK_COMB (@lem4018412 _101783 _101790 _46399 _46400) (@lem4018418 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4018422 (x : Prop) : (x = x) = True.
Proof. exact (@lem4018421 Prop x). Qed.
Lemma lem4018423 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : ((term218 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400)) = True.
Proof. exact (@lem4018422 (term218 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018424 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : ((term136 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400)) = True.
Proof. exact (TRANS (@lem4018419 _101783 _101790 _46399 _46400) (@lem4018423 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018425 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : True = ((term136 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400)).
Proof. exact (SYM (@lem4018424 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018426 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term136 _101783 _101790 _46399 _46400) = (term218 _101783 _101790 _46399 _46400).
Proof. exact (EQ_MP (@lem4018425 _101783 _101790 _46399 _46400) (@lem0)). Qed.
Lemma lem4018427 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) (h1 : term13 _101783 _101790) : term218 _101783 _101790 _46399 _46400.
Proof. exact (EQ_MP (@lem4018426 _101783 _101790 _46399 _46400) (@lem4018121 _101783 _101790 _46399 _46400 h1)). Qed.
Lemma lem4018429 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4018430 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term218 _101783 _101790 _46399 _46400) = (term221 _101783 _101790 _46399 _46400).
Proof. exact (@lem4018429 (term172 _101783 _46400) (term137 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018432 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018433 {_101783 : Type'} (_46400 : _101783 -> Prop) : (term187 _101783 _46400) = (@FINITE _101783 _46400).
Proof. exact (@lem4018432 (@FINITE _101783 _46400)). Qed.
Lemma lem4018434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018435 {_101783 : Type'} (_46400 : _101783 -> Prop) : (term188 _101783 _46400) = (term189 _101783 _46400).
Proof. exact (MK_COMB (@lem4018434) (@lem4018433 _101783 _46400)). Qed.
Lemma lem4018436 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term137 _101783 _101790 _46399 _46400) = (term137 _101783 _101790 _46399 _46400).
Proof. exact (eq_refl (term137 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018437 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term221 _101783 _101790 _46399 _46400) = (term78 _101783 _101790 _46399 _46400).
Proof. exact (MK_COMB (@lem4018435 _101783 _46400) (@lem4018436 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018438 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) : (term218 _101783 _101790 _46399 _46400) = (term78 _101783 _101790 _46399 _46400).
Proof. exact (TRANS (@lem4018430 _101783 _101790 _46399 _46400) (@lem4018437 _101783 _101790 _46399 _46400)). Qed.
Lemma lem4018441 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) (h1 : term13 _101783 _101790) : term78 _101783 _101790 _46399 _46400.
Proof. exact (EQ_MP (@lem4018438 _101783 _101790 _46399 _46400) (@lem4018427 _101783 _101790 _46399 _46400 h1)). Qed.
Lemma lem4018442 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (_46400 : _101783 -> Prop) (h1 : term13 _101783 _101790) : term78 _101783 _101790 _46399 _46400.
Proof. exact (@lem4018441 _101783 _101790 _46399 _46400 h1). Qed.
Lemma lem4018443 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) : term78 _101783 _101790 _46399 t.
Proof. exact (@lem4018442 _101783 _101790 _46399 t h1). Qed.
Lemma lem4018446 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term137 _101783 _101790 _46399 t.
Proof. exact (@lem4018443 _101783 _101790 _46399 t h1 (@lem4018398 _101783 _101790 f s t h2)). Qed.
Lemma lem4018447 {_101783 _101790 : Type'} (_46399 : _101783 -> _101790) (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term137 _101783 _101790 _46399 t.
Proof. exact (@lem4018446 _101783 _101790 _46399 f s t h1 h2). Qed.
Lemma lem4018448 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term137 _101783 _101790 f t.
Proof. exact (@lem4018447 _101783 _101790 f f s t h1 h2). Qed.
Lemma lem4018449 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term222 _101783 _101790 f t.
Proof. exact (fun h0 : term223 _101783 _101790 f t => @lem4018448 _101783 _101790 f s t h1 h2). Qed.
Lemma lem4018451 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018452 {_101783 _101790 : Type'} (f : _101783 -> _101790) (t : _101783 -> Prop) : (term222 _101783 _101790 f t) = (term137 _101783 _101790 f t).
Proof. exact (@lem4018451 (term137 _101783 _101790 f t)). Qed.
Lemma lem4018453 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term13 _101783 _101790) (h2 : term97 _101783 _101790 f s t) : term137 _101783 _101790 f t.
Proof. exact (EQ_MP (@lem4018452 _101783 _101790 f t) (@lem4018449 _101783 _101790 f s t h1 h2)). Qed.
Lemma lem4018469 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4018470 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term224 _46420 _46419 _46421) = (term225 _46419 _46420 _46421).
Proof. exact (@lem4018469 (Peano.le _46419 _46421) (term174 _46420 _46421)). Qed.
Lemma lem4018476 (_46419 : nat) (_46420 : nat) : (term226 _46419 _46420) = (term226 _46419 _46420).
Proof. exact (eq_refl (term226 _46419 _46420)). Qed.
Lemma lem4018477 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term173 _46420 _46419 _46421) = (term227 _46419 _46420 _46421).
Proof. exact (MK_COMB (@lem4018476 _46419 _46420) (@lem4018470 _46419 _46420 _46421)). Qed.
Lemma lem4018481 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4018482 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term227 _46419 _46420 _46421) = (term228 _46419 _46420 _46421).
Proof. exact (@lem4018481 (Peano.le _46419 _46421) (term174 _46419 _46420) (term174 _46420 _46421)). Qed.
Lemma lem4018498 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term173 _46420 _46419 _46421) = (term228 _46419 _46420 _46421).
Proof. exact (TRANS (@lem4018477 _46419 _46420 _46421) (@lem4018482 _46419 _46420 _46421)). Qed.
Lemma lem4018499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018500 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term229 _46420 _46419 _46421) = (term230 _46419 _46420 _46421).
Proof. exact (MK_COMB (@lem4018499) (@lem4018498 _46419 _46420 _46421)). Qed.
Lemma lem4018516 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term228 _46419 _46420 _46421) = (term228 _46419 _46420 _46421).
Proof. exact (eq_refl (term228 _46419 _46420 _46421)). Qed.
Lemma lem4018517 (_46419 : nat) (_46420 : nat) (_46421 : nat) : ((term173 _46420 _46419 _46421) = (term228 _46419 _46420 _46421)) = ((term228 _46419 _46420 _46421) = (term228 _46419 _46420 _46421)).
Proof. exact (MK_COMB (@lem4018500 _46419 _46420 _46421) (@lem4018516 _46419 _46420 _46421)). Qed.
Lemma lem4018519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4018520 (x : Prop) : (x = x) = True.
Proof. exact (@lem4018519 Prop x). Qed.
Lemma lem4018521 (_46419 : nat) (_46420 : nat) (_46421 : nat) : ((term228 _46419 _46420 _46421) = (term228 _46419 _46420 _46421)) = True.
Proof. exact (@lem4018520 (term228 _46419 _46420 _46421)). Qed.
Lemma lem4018522 (_46419 : nat) (_46420 : nat) (_46421 : nat) : ((term173 _46420 _46419 _46421) = (term228 _46419 _46420 _46421)) = True.
Proof. exact (TRANS (@lem4018517 _46419 _46420 _46421) (@lem4018521 _46419 _46420 _46421)). Qed.
Lemma lem4018523 (_46419 : nat) (_46420 : nat) (_46421 : nat) : True = ((term173 _46420 _46419 _46421) = (term228 _46419 _46420 _46421)).
Proof. exact (SYM (@lem4018522 _46419 _46420 _46421)). Qed.
Lemma lem4018524 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term173 _46420 _46419 _46421) = (term228 _46419 _46420 _46421).
Proof. exact (EQ_MP (@lem4018523 _46419 _46420 _46421) (@lem0)). Qed.
Lemma lem4018525 (_46419 : nat) (_46420 : nat) (_46421 : nat) (h1 : term23) : term228 _46419 _46420 _46421.
Proof. exact (EQ_MP (@lem4018524 _46419 _46420 _46421) (@lem4018187 _46420 _46419 _46421 h1)). Qed.
Lemma lem4018527 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4018528 (_46420 : nat) (_46419 : nat) (_46421 : nat) : (term228 _46419 _46420 _46421) = (term231 _46420 _46419 _46421).
Proof. exact (@lem4018527 (term149 _46419 _46420 _46421) (Peano.le _46419 _46421)). Qed.
Lemma lem4018530 (a : Prop) (b : Prop) : (term204 a b) = (term205 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4018531 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term232 _46419 _46420 _46421) = (term233 _46419 _46420 _46421).
Proof. exact (@lem4018530 (term174 _46419 _46420) (term174 _46420 _46421)). Qed.
Lemma lem4018533 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018534 (_46419 : nat) (_46420 : nat) : (term234 _46419 _46420) = (Peano.le _46419 _46420).
Proof. exact (@lem4018533 (Peano.le _46419 _46420)). Qed.
Lemma lem4018535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018536 (_46419 : nat) (_46420 : nat) : (term235 _46419 _46420) = (term236 _46419 _46420).
Proof. exact (MK_COMB (@lem4018535) (@lem4018534 _46419 _46420)). Qed.
Lemma lem4018538 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4018539 (_46420 : nat) (_46421 : nat) : (term234 _46420 _46421) = (Peano.le _46420 _46421).
Proof. exact (@lem4018538 (Peano.le _46420 _46421)). Qed.
Lemma lem4018540 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term233 _46419 _46420 _46421) = (term154 _46419 _46420 _46421).
Proof. exact (MK_COMB (@lem4018536 _46419 _46420) (@lem4018539 _46420 _46421)). Qed.
Lemma lem4018541 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term232 _46419 _46420 _46421) = (term154 _46419 _46420 _46421).
Proof. exact (TRANS (@lem4018531 _46419 _46420 _46421) (@lem4018540 _46419 _46420 _46421)). Qed.
Lemma lem4018542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018543 (_46419 : nat) (_46420 : nat) (_46421 : nat) : (term237 _46419 _46420 _46421) = (term238 _46419 _46420 _46421).
Proof. exact (MK_COMB (@lem4018542) (@lem4018541 _46419 _46420 _46421)). Qed.
Lemma lem4018544 (_46419 : nat) (_46421 : nat) : (Peano.le _46419 _46421) = (Peano.le _46419 _46421).
Proof. exact (eq_refl (Peano.le _46419 _46421)). Qed.
Lemma lem4018545 (_46420 : nat) (_46419 : nat) (_46421 : nat) : (term231 _46420 _46419 _46421) = (term60 _46420 _46419 _46421).
Proof. exact (MK_COMB (@lem4018543 _46419 _46420 _46421) (@lem4018544 _46419 _46421)). Qed.
Lemma lem4018546 (_46420 : nat) (_46419 : nat) (_46421 : nat) : (term228 _46419 _46420 _46421) = (term60 _46420 _46419 _46421).
Proof. exact (TRANS (@lem4018528 _46420 _46419 _46421) (@lem4018545 _46420 _46419 _46421)). Qed.
Lemma lem4018548 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term97 _101783 _101790 f s t) : term239 _101783 _101790 s f t.
Proof. exact (conj (@lem4018391 _101783 _101790 f s t h1 h3 h4) (@lem4018453 _101783 _101790 f s t h2 h4)). Qed.
Lemma lem4018550 (_46420 : nat) (_46419 : nat) (_46421 : nat) (h1 : term23) : term60 _46420 _46419 _46421.
Proof. exact (EQ_MP (@lem4018546 _46420 _46419 _46421) (@lem4018525 _46419 _46420 _46421 h1)). Qed.
Lemma lem4018551 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term23) : term240 _101783 _101790 f s t.
Proof. exact (@lem4018550 (term241 _101783 _101790 f t) (@CARD _101790 s) (@CARD _101783 t) h1). Qed.
Lemma lem4018554 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : term99 _101783 _101790 s t.
Proof. exact (@lem4018551 _101783 _101790 f s t h4 (@lem4018548 _101783 _101790 f s t h1 h2 h3 h5)). Qed.
Lemma lem4018555 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : term242 _101783 _101790 s t.
Proof. exact (fun h0 : term175 _101783 _101790 s t => @lem4018554 _101783 _101790 f s t h1 h2 h3 h4 h5). Qed.
Lemma lem4018557 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018558 {_101783 _101790 : Type'} (s : _101790 -> Prop) (t : _101783 -> Prop) : (term242 _101783 _101790 s t) = (term99 _101783 _101790 s t).
Proof. exact (@lem4018557 (term99 _101783 _101790 s t)). Qed.
Lemma lem4018559 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : term99 _101783 _101790 s t.
Proof. exact (EQ_MP (@lem4018558 _101783 _101790 s t) (@lem4018555 _101783 _101790 f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem4018562 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4018564 {_101783 _101790 : Type'} (s : _101790 -> Prop) (t : _101783 -> Prop) : (term175 _101783 _101790 s t) = (term243 _101783 _101790 s t).
Proof. exact (@lem4018562 (term99 _101783 _101790 s t)). Qed.
Lemma lem4018567 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term97 _101783 _101790 f s t) : term243 _101783 _101790 s t.
Proof. exact (EQ_MP (@lem4018564 _101783 _101790 s t) (@lem4018189 _101783 _101790 f s t h1)). Qed.
Lemma lem4018570 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : False.
Proof. exact (@lem4018567 _101783 _101790 f s t h5 (@lem4018559 _101783 _101790 f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem4018571 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : term244.
Proof. exact (fun h0 : ~ False => @lem4018570 _101783 _101790 f s t h1 h2 h3 h4 h5). Qed.
Lemma lem4018573 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4018574 : term244 = False.
Proof. exact (@lem4018573 False). Qed.
Lemma lem4018575 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : False.
Proof. exact (EQ_MP (@lem4018574) (@lem4018571 _101783 _101790 f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem4018576 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : (term97 _101783 _101790 f s t) = False.
Proof. exact (prop_ext (fun h6 : term97 _101783 _101790 f s t => @lem4018575 _101783 _101790 f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem4017685 _101783 _101790 f s t h5)). Qed.
Lemma lem4018577 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (t : _101783 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term97 _101783 _101790 f s t) : False.
Proof. exact (EQ_MP (@lem4018576 _101783 _101790 f s t h1 h2 h3 h4 h5) (@lem4017685 _101783 _101790 f s t h5)). Qed.
Lemma lem4018578 {_101783 _101790 : Type'} (f : _101783 -> _101790) (s : _101790 -> Prop) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term108 _101783 _101790 f s) : False.
Proof. exact (ex_elim (@lem4017221 _101783 _101790 f s h5) (fun t : _101783 -> Prop => fun h0 : term107 _101783 _101790 f s t => @lem4018577 _101783 _101790 f s t h1 h2 h3 h4 h0)). Qed.
Lemma lem4018579 {_101783 _101790 : Type'} (f : _101783 -> _101790) (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term115 _101783 _101790 f) : False.
Proof. exact (ex_elim (@lem4017220 _101783 _101790 f h5) (fun s : _101790 -> Prop => fun h0 : term114 _101783 _101790 f s => @lem4018578 _101783 _101790 f s h1 h2 h3 h4 h0)). Qed.
Lemma lem4018580 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term23) (h5 : term10 _101783 _101790) : False.
Proof. exact (ex_elim (@lem4016132 _101783 _101790 h5) (fun f : _101783 -> _101790 => fun h0 : term122 _101783 _101790 f => @lem4018579 _101783 _101790 f h1 h2 h3 h4 h0)). Qed.
Lemma lem4018581 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term10 _101783 _101790) : term21.
Proof. exact (fun h0 : term23 => @lem4018580 _101783 _101790 h1 h2 h3 h0 h4). Qed.
Lemma lem4018582 : term21 = term22.
Proof. exact (@lem69 term23). Qed.
Lemma lem4018583 {_101783 _101790 : Type'} (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term10 _101783 _101790) : term22.
Proof. exact (EQ_MP (@lem4018582) (@lem4018581 _101783 _101790 h1 h2 h3 h4)). Qed.
Lemma lem4018584 {_101783 _101790 A : Type'} (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term10 _101783 _101790) : term26 _101783 A.
Proof. exact (fun h0 : term12 _101783 A => @lem4018583 _101783 _101790 h1 h2 h3 h4). Qed.
Lemma lem4018585 {_101783 _101790 A B : Type'} (h1 : term11 _101783 _101790) (h2 : term13 _101783 _101790) (h3 : term16 _101790) (h4 : term10 _101783 _101790) : term29 _101783 A B.
Proof. exact (fun h0 : term11 _101783 B => @lem4018584 _101783 _101790 A h1 h2 h3 h4). Qed.
Lemma lem4018586 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term31 _101783 _101790 A B.
Proof. exact (fun h0 : term11 _101783 _101790 => @lem4018585 _101783 _101790 A B h0 h1 h2 h3). Qed.
Lemma lem4018587 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term34 _101783 _101790 A B.
Proof. exact (fun h0 : term14 B => @lem4018586 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018588 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term37 _101783 _101790 A B.
Proof. exact (fun h0 : term13 A B => @lem4018587 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018589 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term40 _101783 _101790 A B.
Proof. exact (fun h0 : term15 _101790 A => @lem4018588 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018590 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term42 _101783 _101790 A B.
Proof. exact (fun h0 : term15 _101783 A => @lem4018589 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018591 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term44 _101783 _101790 A B.
Proof. exact (fun h0 : term13 _101790 B => @lem4018590 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018592 {_101783 _101790 A B : Type'} (h1 : term13 _101783 _101790) (h2 : term16 _101790) (h3 : term10 _101783 _101790) : term46 _101783 _101790 A B.
Proof. exact (fun h0 : term13 _101783 B => @lem4018591 _101783 _101790 A B h1 h2 h3). Qed.
Lemma lem4018593 {_101783 _101790 A B : Type'} (h1 : term16 _101790) (h2 : term10 _101783 _101790) : term48 _101783 _101790 A B.
Proof. exact (fun h0 : term13 _101783 _101790 => @lem4018592 _101783 _101790 A B h0 h1 h2). Qed.
Lemma lem4018594 {_101783 _101790 A B : Type'} (h1 : term16 _101790) (h2 : term10 _101783 _101790) : term51 _101783 _101790 A B.
Proof. exact (fun h0 : term16 B => @lem4018593 _101783 _101790 A B h1 h2). Qed.
Lemma lem4018595 {_101783 _101790 A B : Type'} (h1 : term16 _101790) (h2 : term10 _101783 _101790) : term53 _101783 _101790 A B.
Proof. exact (fun h0 : term16 A => @lem4018594 _101783 _101790 A B h1 h2). Qed.
Lemma lem4018596 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term55 _101783 _101790 A B.
Proof. exact (fun h0 : term16 _101790 => @lem4018595 _101783 _101790 A B h0 h1). Qed.
Lemma lem4018597 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term57 _101783 _101790 A B.
Proof. exact (fun h0 : term16 _101783 => @lem4018596 _101783 _101790 A B h1). Qed.
Lemma lem4018598 {_101783 _101790 A B : Type'} : term59 _101783 _101790 A B.
Proof. exact (fun h0 : term10 _101783 _101790 => @lem4018597 _101783 _101790 A B h0). Qed.
Lemma lem4018599 {_101783 _101790 A B : Type'} : term17 _101783 _101790 A B.
Proof. exact (EQ_MP (@lem4016014 _101783 _101790 A B) (@lem4018598 _101783 _101790 A B)). Qed.
Lemma lem4018601 {_101783 _101790 A B : Type'} : term17 _101783 _101790 A B.
Proof. exact (@lem4015200 _101783 _101790 A B (@lem4018599 _101783 _101790 A B)). Qed.
Lemma lem4018602 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term56 _101783 _101790 A B.
Proof. exact (@lem4018601 _101783 _101790 A B (@lem4015161 _101783 _101790 h1)). Qed.
Lemma lem4018603 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term54 _101783 _101790 A B.
Proof. exact (@lem4018602 _101783 _101790 A B h1 (@lem4015177 _101783)). Qed.
Lemma lem4018604 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term52 _101783 _101790 A B.
Proof. exact (@lem4018603 _101783 _101790 A B h1 (@lem4015176 _101790)). Qed.
Lemma lem4018605 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term50 _101783 _101790 A B.
Proof. exact (@lem4018604 _101783 _101790 A B h1 (@lem4015178 A)). Qed.
Lemma lem4018606 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term47 _101783 _101790 A B.
Proof. exact (@lem4018605 _101783 _101790 A B h1 (@lem4015179 B)). Qed.
Lemma lem4018607 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term45 _101783 _101790 A B.
Proof. exact (@lem4018606 _101783 _101790 A B h1 (@lem4015171 _101783 _101790)). Qed.
Lemma lem4018608 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term43 _101783 _101790 A B.
Proof. exact (@lem4018607 _101783 _101790 A B h1 (@lem4015165 _101783 B)). Qed.
Lemma lem4018609 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term41 _101783 _101790 A B.
Proof. exact (@lem4018608 _101783 _101790 A B h1 (@lem4015168 _101790 B)). Qed.
Lemma lem4018610 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term39 _101783 _101790 A B.
Proof. exact (@lem4018609 _101783 _101790 A B h1 (@lem4015170 _101783 A)). Qed.
Lemma lem4018611 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term36 _101783 _101790 A B.
Proof. exact (@lem4018610 _101783 _101790 A B h1 (@lem4015169 _101790 A)). Qed.
Lemma lem4018612 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term33 _101783 _101790 A B.
Proof. exact (@lem4018611 _101783 _101790 A B h1 (@lem4015166 A B)). Qed.
Lemma lem4018613 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term30 _101783 _101790 A B.
Proof. exact (@lem4018612 _101783 _101790 A B h1 (@lem4015167 B)). Qed.
Lemma lem4018614 {_101783 _101790 A B : Type'} (h1 : term10 _101783 _101790) : term28 _101783 A B.
Proof. exact (@lem4018613 _101783 _101790 A B h1 (@lem4015164 _101783 _101790)). Qed.
Lemma lem4018615 {_101783 _101790 A : Type'} (h1 : term10 _101783 _101790) : term25 _101783 A.
Proof. exact (@lem4018614 _101783 _101790 A Prop h1 (@lem4015162 _101783 Prop)). Qed.
Lemma lem4018616 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : term21.
Proof. exact (@lem4018615 _101783 _101790 Prop h1 (@lem4015163 _101783 Prop)). Qed.
Lemma lem4018617 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : False.
Proof. exact (@lem4018616 _101783 _101790 h1 (@lem93743)). Qed.
Lemma lem4018618 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : (term10 _101783 _101790) = False.
Proof. exact (prop_ext (fun h2 : term10 _101783 _101790 => @lem4018617 _101783 _101790 h1) (fun h2 : False => @lem4015161 _101783 _101790 h1)). Qed.
Lemma lem4018619 {_101783 _101790 : Type'} (h1 : term10 _101783 _101790) : False.
Proof. exact (EQ_MP (@lem4018618 _101783 _101790 h1) (@lem4015161 _101783 _101790 h1)). Qed.
Lemma lem4018620 {_101783 _101790 : Type'} : term9 _101783 _101790.
Proof. exact (fun h0 : term10 _101783 _101790 => @lem4018619 _101783 _101790 h0). Qed.
Lemma lem4018621 {_101783 _101790 : Type'} : term8 _101783 _101790.
Proof. exact (EQ_MP (@lem4015160 _101783 _101790) (@lem4018620 _101783 _101790)). Qed.
