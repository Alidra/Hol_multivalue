Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7933216 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7933217 : (@FINITE unit (@UNIV unit)) = term1.
Proof. exact (@lem7933216 (@FINITE unit (@UNIV unit))). Qed.
Lemma lem7933218 : term1 = (@FINITE unit (@UNIV unit)).
Proof. exact (SYM (@lem7933217)). Qed.
Lemma lem7933219 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem7933220 : term3.
Proof. exact (@lem3863773 unit). Qed.
Lemma lem7933224 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem7933225 : term5.
Proof. exact (fun h0 : term4 => @lem7933224 h0). Qed.
Lemma lem7933226 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem7933227 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem7933228 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem7933226 h2 (@lem7933227 h1)). Qed.
Lemma lem7933229 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem7933228 h1 h0). Qed.
Lemma lem7933230 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem7933231 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem7933229 h1 (@lem7933230 h2)). Qed.
Lemma lem7933232 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem7933231 h0 h1). Qed.
Lemma lem7933233 : term7.
Proof. exact (fun h0 : term5 => @lem7933232 h0). Qed.
Lemma lem7933236 : term5.
Proof. exact (@lem7933233 (@lem7933225)). Qed.
Lemma lem7933252 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7933253 : term8 = term9.
Proof. exact (@lem7933252 term10). Qed.
Lemma lem7933254 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem7933255 : term12 = term13.
Proof. exact (MK_COMB (@lem7933254) (@lem7933253)). Qed.
Lemma lem7933258 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7933265 : term4 = term15.
Proof. exact (MK_COMB (@lem7933258) (@lem7933255)). Qed.
Lemma lem7933268 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem7933277 (s : unit -> Prop) (n : nat) : ((@HAS_SIZE unit s n) = (term16 s n)) = ((@HAS_SIZE unit s n) = (term16 s n)).
Proof. exact (eq_refl ((@HAS_SIZE unit s n) = (term16 s n))). Qed.
Lemma lem7933278 (s : unit -> Prop) : (term17 s) = (term17 s).
Proof. exact (fun_ext (fun n : nat => @lem7933277 s n)). Qed.
Lemma lem7933279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933280 (s : unit -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem7933279) (@lem7933278 s)). Qed.
Lemma lem7933281 : term19 = term19.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933280 s)). Qed.
Lemma lem7933282 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933283 : term3 = term3.
Proof. exact (MK_COMB (@lem7933282) (@lem7933281)). Qed.
Lemma lem7933284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7933285 : term11 = term11.
Proof. exact (MK_COMB (@lem7933284) (@lem7933283)). Qed.
Lemma lem7933286 : term13 = term13.
Proof. exact (MK_COMB (@lem7933285) (@lem7933268)). Qed.
Lemma lem7933291 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7933292 : term15 = term15.
Proof. exact (MK_COMB (@lem7933291) (@lem7933286)). Qed.
Lemma lem7933313 : term4 = term15.
Proof. exact (TRANS (@lem7933265) (@lem7933292)). Qed.
Lemma lem7933314 : term15 = term4.
Proof. exact (SYM (@lem7933313)). Qed.
Lemma lem7933316 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem7933323 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem7933334 (s : unit -> Prop) (n : nat) : (term20 s n) = (term21 s n).
Proof. exact (@lem17045 (@FINITE unit s) ((@CARD unit s) = n)). Qed.
Lemma lem7933340 (s : unit -> Prop) (n : nat) : (term22 s n) = (term22 s n).
Proof. exact (eq_refl (term22 s n)). Qed.
Lemma lem7933342 (s : unit -> Prop) (n : nat) : (term23 s n) = (term23 s n).
Proof. exact (eq_refl (term23 s n)). Qed.
Lemma lem7933343 (s : unit -> Prop) (n : nat) : (term24 s n) = (term25 s n).
Proof. exact (MK_COMB (@lem7933342 s n) (@lem7933334 s n)). Qed.
Lemma lem7933344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933345 (s : unit -> Prop) (n : nat) : (term26 s n) = (term27 s n).
Proof. exact (MK_COMB (@lem7933344) (@lem7933343 s n)). Qed.
Lemma lem7933346 (s : unit -> Prop) (n : nat) : (term28 s n) = (term29 s n).
Proof. exact (MK_COMB (@lem7933345 s n) (@lem7933340 s n)). Qed.
Lemma lem7933347 (s : unit -> Prop) (n : nat) : ((@HAS_SIZE unit s n) = (term16 s n)) = (term28 s n).
Proof. exact (@lem17784 (@HAS_SIZE unit s n) (term16 s n)). Qed.
Lemma lem7933348 (s : unit -> Prop) (n : nat) : ((@HAS_SIZE unit s n) = (term16 s n)) = (term29 s n).
Proof. exact (TRANS (@lem7933347 s n) (@lem7933346 s n)). Qed.
Lemma lem7933349 (s : unit -> Prop) : (term17 s) = (term30 s).
Proof. exact (fun_ext (fun n : nat => @lem7933348 s n)). Qed.
Lemma lem7933350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933351 (s : unit -> Prop) : (term18 s) = (term31 s).
Proof. exact (MK_COMB (@lem7933350) (@lem7933349 s)). Qed.
Lemma lem7933352 : term19 = term32.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933351 s)). Qed.
Lemma lem7933353 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933354 : term3 = term33.
Proof. exact (MK_COMB (@lem7933353) (@lem7933352)). Qed.
Lemma lem7933360 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7933361 (P : nat -> Prop) (Q : nat -> Prop) : (term36 P Q) = (term37 P Q).
Proof. exact (@lem7933360 nat P Q). Qed.
Lemma lem7933362 (s : unit -> Prop) : (term38 s) = (term39 s).
Proof. exact (@lem7933361 (term40 s) (term41 s)). Qed.
Lemma lem7933363 (s : unit -> Prop) (n : nat) : (term42 s n) = (term25 s n).
Proof. exact (eq_refl (term42 s n)). Qed.
Lemma lem7933364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933365 (s : unit -> Prop) (n : nat) : (term43 s n) = (term27 s n).
Proof. exact (MK_COMB (@lem7933364) (@lem7933363 s n)). Qed.
Lemma lem7933366 (s : unit -> Prop) (n : nat) : (term44 s n) = (term22 s n).
Proof. exact (eq_refl (term44 s n)). Qed.
Lemma lem7933367 (s : unit -> Prop) (n : nat) : (term45 s n) = (term29 s n).
Proof. exact (MK_COMB (@lem7933365 s n) (@lem7933366 s n)). Qed.
Lemma lem7933368 (s : unit -> Prop) : (term46 s) = (term30 s).
Proof. exact (fun_ext (fun n : nat => @lem7933367 s n)). Qed.
Lemma lem7933369 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933370 (s : unit -> Prop) : (term38 s) = (term31 s).
Proof. exact (MK_COMB (@lem7933369) (@lem7933368 s)). Qed.
Lemma lem7933371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7933372 (s : unit -> Prop) : (term47 s) = (term48 s).
Proof. exact (MK_COMB (@lem7933371) (@lem7933370 s)). Qed.
Lemma lem7933373 (s : unit -> Prop) (n : nat) : (term42 s n) = (term25 s n).
Proof. exact (eq_refl (term42 s n)). Qed.
Lemma lem7933374 (s : unit -> Prop) : (term49 s) = (term40 s).
Proof. exact (fun_ext (fun n : nat => @lem7933373 s n)). Qed.
Lemma lem7933375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933376 (s : unit -> Prop) : (term50 s) = (term51 s).
Proof. exact (MK_COMB (@lem7933375) (@lem7933374 s)). Qed.
Lemma lem7933377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933378 (s : unit -> Prop) : (term52 s) = (term53 s).
Proof. exact (MK_COMB (@lem7933377) (@lem7933376 s)). Qed.
Lemma lem7933379 (s : unit -> Prop) (n : nat) : (term44 s n) = (term22 s n).
Proof. exact (eq_refl (term44 s n)). Qed.
Lemma lem7933380 (s : unit -> Prop) : (term54 s) = (term41 s).
Proof. exact (fun_ext (fun n : nat => @lem7933379 s n)). Qed.
Lemma lem7933381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933382 (s : unit -> Prop) : (term55 s) = (term56 s).
Proof. exact (MK_COMB (@lem7933381) (@lem7933380 s)). Qed.
Lemma lem7933383 (s : unit -> Prop) : (term39 s) = (term57 s).
Proof. exact (MK_COMB (@lem7933378 s) (@lem7933382 s)). Qed.
Lemma lem7933384 (s : unit -> Prop) : ((term38 s) = (term39 s)) = ((term31 s) = (term57 s)).
Proof. exact (MK_COMB (@lem7933372 s) (@lem7933383 s)). Qed.
Lemma lem7933385 (s : unit -> Prop) : (term31 s) = (term57 s).
Proof. exact (EQ_MP (@lem7933384 s) (@lem7933362 s)). Qed.
Lemma lem7933482 : term32 = term58.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933385 s)). Qed.
Lemma lem7933483 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933484 : term33 = term59.
Proof. exact (MK_COMB (@lem7933483) (@lem7933482)). Qed.
Lemma lem7933486 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7933487 (P : type389) (Q : type389) : (term60 P Q) = (term61 P Q).
Proof. exact (@lem7933486 (unit -> Prop) P Q). Qed.
Lemma lem7933488 : term62 = term63.
Proof. exact (@lem7933487 term64 term65). Qed.
Lemma lem7933489 (s : unit -> Prop) : (term66 s) = (term51 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem7933490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933491 (s : unit -> Prop) : (term67 s) = (term53 s).
Proof. exact (MK_COMB (@lem7933490) (@lem7933489 s)). Qed.
Lemma lem7933492 (s : unit -> Prop) : (term68 s) = (term56 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem7933493 (s : unit -> Prop) : (term69 s) = (term57 s).
Proof. exact (MK_COMB (@lem7933491 s) (@lem7933492 s)). Qed.
Lemma lem7933494 : term70 = term58.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933493 s)). Qed.
Lemma lem7933495 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933496 : term62 = term59.
Proof. exact (MK_COMB (@lem7933495) (@lem7933494)). Qed.
Lemma lem7933497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7933498 : term71 = term72.
Proof. exact (MK_COMB (@lem7933497) (@lem7933496)). Qed.
Lemma lem7933499 (s : unit -> Prop) : (term66 s) = (term51 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem7933500 : term73 = term64.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933499 s)). Qed.
Lemma lem7933501 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933502 : term74 = term75.
Proof. exact (MK_COMB (@lem7933501) (@lem7933500)). Qed.
Lemma lem7933503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933504 : term76 = term77.
Proof. exact (MK_COMB (@lem7933503) (@lem7933502)). Qed.
Lemma lem7933505 (s : unit -> Prop) : (term68 s) = (term56 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem7933506 : term78 = term65.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933505 s)). Qed.
Lemma lem7933507 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933508 : term79 = term80.
Proof. exact (MK_COMB (@lem7933507) (@lem7933506)). Qed.
Lemma lem7933509 : term63 = term81.
Proof. exact (MK_COMB (@lem7933504) (@lem7933508)). Qed.
Lemma lem7933510 : (term62 = term63) = (term59 = term81).
Proof. exact (MK_COMB (@lem7933498) (@lem7933509)). Qed.
Lemma lem7933511 : term59 = term81.
Proof. exact (EQ_MP (@lem7933510) (@lem7933488)). Qed.
Lemma lem7933618 : term33 = term81.
Proof. exact (TRANS (@lem7933484) (@lem7933511)). Qed.
Lemma lem7933619 : term3 = term81.
Proof. exact (TRANS (@lem7933354) (@lem7933618)). Qed.
Lemma lem7933620 (h1 : term3) : term81.
Proof. exact (EQ_MP (@lem7933619) (@lem7933316 h1)). Qed.
Lemma lem7933626 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7933632 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem7933655 (s : unit -> Prop) (n : nat) : (term22 s n) = (term22 s n).
Proof. exact (eq_refl (term22 s n)). Qed.
Lemma lem7933656 (s : unit -> Prop) : (term41 s) = (term41 s).
Proof. exact (fun_ext (fun n : nat => @lem7933655 s n)). Qed.
Lemma lem7933657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933658 (s : unit -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem7933657) (@lem7933656 s)). Qed.
Lemma lem7933659 : term65 = term65.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933658 s)). Qed.
Lemma lem7933660 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933661 : term80 = term80.
Proof. exact (MK_COMB (@lem7933660) (@lem7933659)). Qed.
Lemma lem7933686 (s : unit -> Prop) (n : nat) : (term25 s n) = (term25 s n).
Proof. exact (eq_refl (term25 s n)). Qed.
Lemma lem7933687 (s : unit -> Prop) : (term40 s) = (term40 s).
Proof. exact (fun_ext (fun n : nat => @lem7933686 s n)). Qed.
Lemma lem7933688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933689 (s : unit -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem7933688) (@lem7933687 s)). Qed.
Lemma lem7933690 : term64 = term64.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933689 s)). Qed.
Lemma lem7933691 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933692 : term75 = term75.
Proof. exact (MK_COMB (@lem7933691) (@lem7933690)). Qed.
Lemma lem7933693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933694 : term77 = term77.
Proof. exact (MK_COMB (@lem7933693) (@lem7933692)). Qed.
Lemma lem7933695 : term81 = term81.
Proof. exact (MK_COMB (@lem7933694) (@lem7933661)). Qed.
Lemma lem7933696 (h1 : term3) : term81.
Proof. exact (EQ_MP (@lem7933695) (@lem7933620 h1)). Qed.
Lemma lem7933706 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7933707 (h1 : term3) : term80.
Proof. exact (proj2 (@lem7933696 h1)). Qed.
Lemma lem7933712 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem7933716 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7933756 (s : unit -> Prop) (n : nat) : (term22 s n) = (term82 s n).
Proof. exact (@lem19490 (@FINITE unit s) (term83 s n) ((@CARD unit s) = n)). Qed.
Lemma lem7933757 (s : unit -> Prop) : (term41 s) = (term84 s).
Proof. exact (fun_ext (fun n : nat => @lem7933756 s n)). Qed.
Lemma lem7933758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7933759 (s : unit -> Prop) : (term56 s) = (term85 s).
Proof. exact (MK_COMB (@lem7933758) (@lem7933757 s)). Qed.
Lemma lem7933760 : term65 = term86.
Proof. exact (fun_ext (fun s : unit -> Prop => @lem7933759 s)). Qed.
Lemma lem7933761 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem7933763 : term80 = term87.
Proof. exact (MK_COMB (@lem7933761) (@lem7933760)). Qed.
Lemma lem7933764 (h1 : term3) : term87.
Proof. exact (EQ_MP (@lem7933763) (@lem7933707 h1)). Qed.
Lemma lem7933771 (_103839 : unit -> Prop) (h1 : term3) : term88 _103839.
Proof. exact (@lem7933764 h1 _103839). Qed.
Lemma lem7933772 (_103839 : unit -> Prop) : (term88 _103839) = (term85 _103839).
Proof. exact (eq_refl (term88 _103839)). Qed.
Lemma lem7933773 (_103839 : unit -> Prop) (h1 : term3) : term85 _103839.
Proof. exact (EQ_MP (@lem7933772 _103839) (@lem7933771 _103839 h1)). Qed.
Lemma lem7933774 (_103839 : unit -> Prop) (_103840 : nat) (h1 : term3) : term89 _103839 _103840.
Proof. exact (@lem7933773 _103839 h1 _103840). Qed.
Lemma lem7933775 (_103839 : unit -> Prop) (_103840 : nat) : (term89 _103839 _103840) = (term82 _103839 _103840).
Proof. exact (eq_refl (term89 _103839 _103840)). Qed.
Lemma lem7933776 (_103839 : unit -> Prop) (_103840 : nat) (h1 : term3) : term82 _103839 _103840.
Proof. exact (EQ_MP (@lem7933775 _103839 _103840) (@lem7933774 _103839 _103840 h1)). Qed.
Lemma lem7933780 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem7933782 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7933798 (_103840 : nat) (_103839 : unit -> Prop) (h1 : term3) : term90 _103840 _103839.
Proof. exact (proj1 (@lem7933776 _103839 _103840 h1)). Qed.
Lemma lem7933865 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7933866 (h1 : term10) : term91.
Proof. exact (fun h0 : term9 => @lem7933865 h1). Qed.
Lemma lem7933868 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7933869 : term91 = term10.
Proof. exact (@lem7933868 term10). Qed.
Lemma lem7933870 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem7933869) (@lem7933866 h1)). Qed.
Lemma lem7933876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7933877 (_103839 : unit -> Prop) (_103840 : nat) : (term90 _103840 _103839) = (term93 _103839 _103840).
Proof. exact (@lem7933876 (@FINITE unit _103839) (term83 _103839 _103840)). Qed.
Lemma lem7933883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7933884 (_103839 : unit -> Prop) (_103840 : nat) : (term94 _103840 _103839) = (term95 _103839 _103840).
Proof. exact (MK_COMB (@lem7933883) (@lem7933877 _103839 _103840)). Qed.
Lemma lem7933890 (_103839 : unit -> Prop) (_103840 : nat) : (term93 _103839 _103840) = (term93 _103839 _103840).
Proof. exact (eq_refl (term93 _103839 _103840)). Qed.
Lemma lem7933891 (_103839 : unit -> Prop) (_103840 : nat) : ((term90 _103840 _103839) = (term93 _103839 _103840)) = ((term93 _103839 _103840) = (term93 _103839 _103840)).
Proof. exact (MK_COMB (@lem7933884 _103839 _103840) (@lem7933890 _103839 _103840)). Qed.
Lemma lem7933893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7933894 (x : Prop) : (x = x) = True.
Proof. exact (@lem7933893 Prop x). Qed.
Lemma lem7933895 (_103839 : unit -> Prop) (_103840 : nat) : ((term93 _103839 _103840) = (term93 _103839 _103840)) = True.
Proof. exact (@lem7933894 (term93 _103839 _103840)). Qed.
Lemma lem7933896 (_103839 : unit -> Prop) (_103840 : nat) : ((term90 _103840 _103839) = (term93 _103839 _103840)) = True.
Proof. exact (TRANS (@lem7933891 _103839 _103840) (@lem7933895 _103839 _103840)). Qed.
Lemma lem7933897 (_103839 : unit -> Prop) (_103840 : nat) : True = ((term90 _103840 _103839) = (term93 _103839 _103840)).
Proof. exact (SYM (@lem7933896 _103839 _103840)). Qed.
Lemma lem7933898 (_103839 : unit -> Prop) (_103840 : nat) : (term90 _103840 _103839) = (term93 _103839 _103840).
Proof. exact (EQ_MP (@lem7933897 _103839 _103840) (@lem0)). Qed.
Lemma lem7933899 (_103839 : unit -> Prop) (_103840 : nat) (h1 : term3) : term93 _103839 _103840.
Proof. exact (EQ_MP (@lem7933898 _103839 _103840) (@lem7933798 _103840 _103839 h1)). Qed.
Lemma lem7933901 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7933902 (_103840 : nat) (_103839 : unit -> Prop) : (term93 _103839 _103840) = (term97 _103840 _103839).
Proof. exact (@lem7933901 (term83 _103839 _103840) (@FINITE unit _103839)). Qed.
Lemma lem7933904 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7933905 (_103839 : unit -> Prop) (_103840 : nat) : (term99 _103839 _103840) = (@HAS_SIZE unit _103839 _103840).
Proof. exact (@lem7933904 (@HAS_SIZE unit _103839 _103840)). Qed.
Lemma lem7933906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7933907 (_103839 : unit -> Prop) (_103840 : nat) : (term100 _103839 _103840) = (term101 _103839 _103840).
Proof. exact (MK_COMB (@lem7933906) (@lem7933905 _103839 _103840)). Qed.
Lemma lem7933908 (_103839 : unit -> Prop) : (@FINITE unit _103839) = (@FINITE unit _103839).
Proof. exact (eq_refl (@FINITE unit _103839)). Qed.
Lemma lem7933909 (_103840 : nat) (_103839 : unit -> Prop) : (term97 _103840 _103839) = (term102 _103840 _103839).
Proof. exact (MK_COMB (@lem7933907 _103839 _103840) (@lem7933908 _103839)). Qed.
Lemma lem7933910 (_103840 : nat) (_103839 : unit -> Prop) : (term93 _103839 _103840) = (term102 _103840 _103839).
Proof. exact (TRANS (@lem7933902 _103840 _103839) (@lem7933909 _103840 _103839)). Qed.
Lemma lem7933913 (_103840 : nat) (_103839 : unit -> Prop) (h1 : term3) : term102 _103840 _103839.
Proof. exact (EQ_MP (@lem7933910 _103840 _103839) (@lem7933899 _103839 _103840 h1)). Qed.
Lemma lem7933914 (h1 : term3) : term103.
Proof. exact (@lem7933913 term104 (@UNIV unit) h1). Qed.
Lemma lem7933917 (h1 : term3) (h2 : term10) : @FINITE unit (@UNIV unit).
Proof. exact (@lem7933914 h1 (@lem7933870 h2)). Qed.
Lemma lem7933918 (h1 : term3) (h2 : term10) : term105.
Proof. exact (fun h0 : term2 => @lem7933917 h1 h2). Qed.
Lemma lem7933920 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7933921 : term105 = (@FINITE unit (@UNIV unit)).
Proof. exact (@lem7933920 (@FINITE unit (@UNIV unit))). Qed.
Lemma lem7933922 (h1 : term3) (h2 : term10) : @FINITE unit (@UNIV unit).
Proof. exact (EQ_MP (@lem7933921) (@lem7933918 h1 h2)). Qed.
Lemma lem7933925 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7933927 : term2 = term106.
Proof. exact (@lem7933925 (@FINITE unit (@UNIV unit))). Qed.
Lemma lem7933930 (h1 : term2) : term106.
Proof. exact (EQ_MP (@lem7933927) (@lem7933780 h1)). Qed.
Lemma lem7933933 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (@lem7933930 h2 (@lem7933922 h1 h3)). Qed.
Lemma lem7933934 (h1 : term3) (h2 : term2) (h3 : term10) : term107.
Proof. exact (fun h0 : ~ False => @lem7933933 h1 h2 h3). Qed.
Lemma lem7933936 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7933937 : term107 = False.
Proof. exact (@lem7933936 False). Qed.
Lemma lem7933938 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933937) (@lem7933934 h1 h2 h3)). Qed.
Lemma lem7933939 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem7933938 h1 h2 h3) (fun h4 : False => @lem7933782 h3)). Qed.
Lemma lem7933940 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933939 h1 h2 h3) (@lem7933782 h3)). Qed.
Lemma lem7933941 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem7933940 h1 h2 h3) (fun h4 : False => @lem7933780 h2)). Qed.
Lemma lem7933942 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933941 h1 h2 h3) (@lem7933780 h2)). Qed.
Lemma lem7933943 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem7933942 h1 h2 h3) (fun h4 : False => @lem7933716 h3)). Qed.
Lemma lem7933944 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933943 h1 h2 h3) (@lem7933716 h3)). Qed.
Lemma lem7933945 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem7933944 h1 h2 h3) (fun h4 : False => @lem7933712 h2)). Qed.
Lemma lem7933946 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933945 h1 h2 h3) (@lem7933712 h2)). Qed.
Lemma lem7933947 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem7933946 h1 h2 h3) (fun h4 : False => @lem7933716 h3)). Qed.
Lemma lem7933948 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933947 h1 h2 h3) (@lem7933716 h3)). Qed.
Lemma lem7933949 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem7933948 h1 h2 h3) (fun h4 : False => @lem7933712 h2)). Qed.
Lemma lem7933950 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933949 h1 h2 h3) (@lem7933712 h2)). Qed.
Lemma lem7933951 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem7933950 h1 h2 h3) (fun h4 : False => @lem7933706 h3)). Qed.
Lemma lem7933952 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933951 h1 h2 h3) (@lem7933706 h3)). Qed.
Lemma lem7933953 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem7933952 h1 h2 h3) (fun h4 : False => @lem7933632 h2)). Qed.
Lemma lem7933954 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933953 h1 h2 h3) (@lem7933632 h2)). Qed.
Lemma lem7933955 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem7933954 h1 h2 h3) (fun h4 : False => @lem7933626 h3)). Qed.
Lemma lem7933956 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933955 h1 h2 h3) (@lem7933626 h3)). Qed.
Lemma lem7933957 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem7933956 h1 h2 h3) (fun h4 : False => @lem7933323 h2)). Qed.
Lemma lem7933958 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem7933957 h1 h2 h3) (@lem7933323 h2)). Qed.
Lemma lem7933959 (h1 : term3) (h2 : term2) : term8.
Proof. exact (fun h0 : term10 => @lem7933958 h1 h2 h0). Qed.
Lemma lem7933960 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem7933961 (h1 : term3) (h2 : term2) : term9.
Proof. exact (EQ_MP (@lem7933960) (@lem7933959 h1 h2)). Qed.
Lemma lem7933962 (h1 : term2) : term13.
Proof. exact (fun h0 : term3 => @lem7933961 h0 h1). Qed.
Lemma lem7933963 : term15.
Proof. exact (fun h0 : term2 => @lem7933962 h0). Qed.
Lemma lem7933964 : term4.
Proof. exact (EQ_MP (@lem7933314) (@lem7933963)). Qed.
Lemma lem7933966 : term4.
Proof. exact (@lem7933236 (@lem7933964)). Qed.
Lemma lem7933967 (h1 : term2) : term12.
Proof. exact (@lem7933966 (@lem7933219 h1)). Qed.
Lemma lem7933968 (h1 : term2) : term8.
Proof. exact (@lem7933967 h1 (@lem7933220)). Qed.
Lemma lem7933969 (h1 : term2) : False.
Proof. exact (@lem7933968 h1 (@lem7603370)). Qed.
Lemma lem7933970 (h1 : term2) : term2 = False.
Proof. exact (prop_ext (fun h2 : term2 => @lem7933969 h1) (fun h2 : False => @lem7933219 h1)). Qed.
Lemma lem7933971 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem7933970 h1) (@lem7933219 h1)). Qed.
Lemma lem7933972 : term1.
Proof. exact (fun h0 : term2 => @lem7933971 h0). Qed.
Lemma lem7933973 : @FINITE unit (@UNIV unit).
Proof. exact (EQ_MP (@lem7933218) (@lem7933972)). Qed.
