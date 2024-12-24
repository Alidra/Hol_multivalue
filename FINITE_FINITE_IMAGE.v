Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_FINITE_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_FINITE_IMAGE_spec.
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
Lemma lem7607148 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7607149 {A : Type'} : (@FINITE (finite_image A) (@UNIV (finite_image A))) = (term1 A).
Proof. exact (@lem7607148 (@FINITE (finite_image A) (@UNIV (finite_image A)))). Qed.
Lemma lem7607150 {A : Type'} : (term1 A) = (@FINITE (finite_image A) (@UNIV (finite_image A))).
Proof. exact (SYM (@lem7607149 A)). Qed.
Lemma lem7607151 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7607152 {A : Type'} : term3 A.
Proof. exact (@lem7605765 A). Qed.
Lemma lem7607153 {A : Type'} : term4 A.
Proof. exact (@lem3863773 (finite_image A)). Qed.
Lemma lem7607157 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7607158 {A : Type'} : term6 A.
Proof. exact (fun h0 : term5 A => @lem7607157 A h0). Qed.
Lemma lem7607159 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7607160 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7607161 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7607159 A h2 (@lem7607160 A h1)). Qed.
Lemma lem7607162 {A : Type'} (h1 : term5 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem7607161 A h1 h0). Qed.
Lemma lem7607163 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7607164 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7607162 A h1 (@lem7607163 A h2)). Qed.
Lemma lem7607165 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun h0 : term5 A => @lem7607164 A h0 h1). Qed.
Lemma lem7607166 {A : Type'} : term8 A.
Proof. exact (fun h0 : term6 A => @lem7607165 A h0). Qed.
Lemma lem7607169 {A : Type'} : term6 A.
Proof. exact (@lem7607166 A (@lem7607158 A)). Qed.
Lemma lem7607170 {A : Type'} : term6 A.
Proof. exact (@lem7607169 A). Qed.
Lemma lem7607186 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7607187 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem7607186 (term3 A)). Qed.
Lemma lem7607192 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem7607193 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem7607192 A) (@lem7607187 A)). Qed.
Lemma lem7607196 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (eq_refl (term14 A)). Qed.
Lemma lem7607203 {A : Type'} : (term5 A) = (term15 A).
Proof. exact (MK_COMB (@lem7607196 A) (@lem7607193 A)). Qed.
Lemma lem7607204 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7607205 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7607204 A s)). Qed.
Lemma lem7607206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7607207 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7607206 A) (@lem7607205 A)). Qed.
Lemma lem7607208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7607209 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7607208) (@lem7607207 A)). Qed.
Lemma lem7607218 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term18 A s n)) = ((@HAS_SIZE (finite_image A) s n) = (term18 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (finite_image A) s n) = (term18 A s n))). Qed.
Lemma lem7607219 {A : Type'} (s : type33 A) : (term19 A s) = (term19 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607218 A s n)). Qed.
Lemma lem7607220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607221 {A : Type'} (s : type33 A) : (term20 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem7607220) (@lem7607219 A s)). Qed.
Lemma lem7607222 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607221 A s)). Qed.
Lemma lem7607223 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607224 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7607223 A) (@lem7607222 A)). Qed.
Lemma lem7607225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7607226 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7607225) (@lem7607224 A)). Qed.
Lemma lem7607227 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem7607226 A) (@lem7607209 A)). Qed.
Lemma lem7607232 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (eq_refl (term14 A)). Qed.
Lemma lem7607233 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem7607232 A) (@lem7607227 A)). Qed.
Lemma lem7607260 {A : Type'} : (term5 A) = (term15 A).
Proof. exact (TRANS (@lem7607203 A) (@lem7607233 A)). Qed.
Lemma lem7607261 {A : Type'} : (term15 A) = (term5 A).
Proof. exact (SYM (@lem7607260 A)). Qed.
Lemma lem7607263 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7607264 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7607270 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7607281 {A : Type'} (s : type33 A) (n : nat) : (term22 A s n) = (term23 A s n).
Proof. exact (@lem17045 (@FINITE (finite_image A) s) ((@CARD (finite_image A) s) = n)). Qed.
Lemma lem7607287 {A : Type'} (s : type33 A) (n : nat) : (term24 A s n) = (term24 A s n).
Proof. exact (eq_refl (term24 A s n)). Qed.
Lemma lem7607289 {A : Type'} (s : type33 A) (n : nat) : (term25 A s n) = (term25 A s n).
Proof. exact (eq_refl (term25 A s n)). Qed.
Lemma lem7607290 {A : Type'} (s : type33 A) (n : nat) : (term26 A s n) = (term27 A s n).
Proof. exact (MK_COMB (@lem7607289 A s n) (@lem7607281 A s n)). Qed.
Lemma lem7607291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607292 {A : Type'} (s : type33 A) (n : nat) : (term28 A s n) = (term29 A s n).
Proof. exact (MK_COMB (@lem7607291) (@lem7607290 A s n)). Qed.
Lemma lem7607293 {A : Type'} (s : type33 A) (n : nat) : (term30 A s n) = (term31 A s n).
Proof. exact (MK_COMB (@lem7607292 A s n) (@lem7607287 A s n)). Qed.
Lemma lem7607294 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term18 A s n)) = (term30 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (finite_image A) s n) (term18 A s n)). Qed.
Lemma lem7607295 {A : Type'} (s : type33 A) (n : nat) : ((@HAS_SIZE (finite_image A) s n) = (term18 A s n)) = (term31 A s n).
Proof. exact (TRANS (@lem7607294 A s n) (@lem7607293 A s n)). Qed.
Lemma lem7607296 {A : Type'} (s : type33 A) : (term19 A s) = (term32 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607295 A s n)). Qed.
Lemma lem7607297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607298 {A : Type'} (s : type33 A) : (term20 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem7607297) (@lem7607296 A s)). Qed.
Lemma lem7607299 {A : Type'} : (term21 A) = (term34 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607298 A s)). Qed.
Lemma lem7607300 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607301 {A : Type'} : (term4 A) = (term35 A).
Proof. exact (MK_COMB (@lem7607300 A) (@lem7607299 A)). Qed.
Lemma lem7607307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term37 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7607308 (P : nat -> Prop) (Q : nat -> Prop) : (term38 P Q) = (term39 P Q).
Proof. exact (@lem7607307 nat P Q). Qed.
Lemma lem7607309 {A : Type'} (s : type33 A) : (term40 A s) = (term41 A s).
Proof. exact (@lem7607308 (term42 A s) (term43 A s)). Qed.
Lemma lem7607310 {A : Type'} (s : type33 A) (n : nat) : (term44 A s n) = (term27 A s n).
Proof. exact (eq_refl (term44 A s n)). Qed.
Lemma lem7607311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607312 {A : Type'} (s : type33 A) (n : nat) : (term45 A s n) = (term29 A s n).
Proof. exact (MK_COMB (@lem7607311) (@lem7607310 A s n)). Qed.
Lemma lem7607313 {A : Type'} (s : type33 A) (n : nat) : (term46 A s n) = (term24 A s n).
Proof. exact (eq_refl (term46 A s n)). Qed.
Lemma lem7607314 {A : Type'} (s : type33 A) (n : nat) : (term47 A s n) = (term31 A s n).
Proof. exact (MK_COMB (@lem7607312 A s n) (@lem7607313 A s n)). Qed.
Lemma lem7607315 {A : Type'} (s : type33 A) : (term48 A s) = (term32 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607314 A s n)). Qed.
Lemma lem7607316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607317 {A : Type'} (s : type33 A) : (term40 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem7607316) (@lem7607315 A s)). Qed.
Lemma lem7607318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7607319 {A : Type'} (s : type33 A) : (term49 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem7607318) (@lem7607317 A s)). Qed.
Lemma lem7607320 {A : Type'} (s : type33 A) (n : nat) : (term44 A s n) = (term27 A s n).
Proof. exact (eq_refl (term44 A s n)). Qed.
Lemma lem7607321 {A : Type'} (s : type33 A) : (term51 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607320 A s n)). Qed.
Lemma lem7607322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607323 {A : Type'} (s : type33 A) : (term52 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem7607322) (@lem7607321 A s)). Qed.
Lemma lem7607324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607325 {A : Type'} (s : type33 A) : (term54 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem7607324) (@lem7607323 A s)). Qed.
Lemma lem7607326 {A : Type'} (s : type33 A) (n : nat) : (term46 A s n) = (term24 A s n).
Proof. exact (eq_refl (term46 A s n)). Qed.
Lemma lem7607327 {A : Type'} (s : type33 A) : (term56 A s) = (term43 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607326 A s n)). Qed.
Lemma lem7607328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607329 {A : Type'} (s : type33 A) : (term57 A s) = (term58 A s).
Proof. exact (MK_COMB (@lem7607328) (@lem7607327 A s)). Qed.
Lemma lem7607330 {A : Type'} (s : type33 A) : (term41 A s) = (term59 A s).
Proof. exact (MK_COMB (@lem7607325 A s) (@lem7607329 A s)). Qed.
Lemma lem7607331 {A : Type'} (s : type33 A) : ((term40 A s) = (term41 A s)) = ((term33 A s) = (term59 A s)).
Proof. exact (MK_COMB (@lem7607319 A s) (@lem7607330 A s)). Qed.
Lemma lem7607332 {A : Type'} (s : type33 A) : (term33 A s) = (term59 A s).
Proof. exact (EQ_MP (@lem7607331 A s) (@lem7607309 A s)). Qed.
Lemma lem7607429 {A : Type'} : (term34 A) = (term60 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607332 A s)). Qed.
Lemma lem7607430 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607431 {A : Type'} : (term35 A) = (term61 A).
Proof. exact (MK_COMB (@lem7607430 A) (@lem7607429 A)). Qed.
Lemma lem7607433 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term37 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7607434 {A : Type'} (P : type59 A) (Q : type59 A) : (term62 A P Q) = (term63 A P Q).
Proof. exact (@lem7607433 (type33 A) P Q). Qed.
Lemma lem7607435 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (@lem7607434 A (term66 A) (term67 A)). Qed.
Lemma lem7607436 {A : Type'} (s : type33 A) : (term68 A s) = (term53 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem7607437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607438 {A : Type'} (s : type33 A) : (term69 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem7607437) (@lem7607436 A s)). Qed.
Lemma lem7607439 {A : Type'} (s : type33 A) : (term70 A s) = (term58 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem7607440 {A : Type'} (s : type33 A) : (term71 A s) = (term59 A s).
Proof. exact (MK_COMB (@lem7607438 A s) (@lem7607439 A s)). Qed.
Lemma lem7607441 {A : Type'} : (term72 A) = (term60 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607440 A s)). Qed.
Lemma lem7607442 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607443 {A : Type'} : (term64 A) = (term61 A).
Proof. exact (MK_COMB (@lem7607442 A) (@lem7607441 A)). Qed.
Lemma lem7607444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7607445 {A : Type'} : (term73 A) = (term74 A).
Proof. exact (MK_COMB (@lem7607444) (@lem7607443 A)). Qed.
Lemma lem7607446 {A : Type'} (s : type33 A) : (term68 A s) = (term53 A s).
Proof. exact (eq_refl (term68 A s)). Qed.
Lemma lem7607447 {A : Type'} : (term75 A) = (term66 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607446 A s)). Qed.
Lemma lem7607448 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607449 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (MK_COMB (@lem7607448 A) (@lem7607447 A)). Qed.
Lemma lem7607450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607451 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (MK_COMB (@lem7607450) (@lem7607449 A)). Qed.
Lemma lem7607452 {A : Type'} (s : type33 A) : (term70 A s) = (term58 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem7607453 {A : Type'} : (term80 A) = (term67 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607452 A s)). Qed.
Lemma lem7607454 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607455 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem7607454 A) (@lem7607453 A)). Qed.
Lemma lem7607456 {A : Type'} : (term65 A) = (term83 A).
Proof. exact (MK_COMB (@lem7607451 A) (@lem7607455 A)). Qed.
Lemma lem7607457 {A : Type'} : ((term64 A) = (term65 A)) = ((term61 A) = (term83 A)).
Proof. exact (MK_COMB (@lem7607445 A) (@lem7607456 A)). Qed.
Lemma lem7607458 {A : Type'} : (term61 A) = (term83 A).
Proof. exact (EQ_MP (@lem7607457 A) (@lem7607435 A)). Qed.
Lemma lem7607565 {A : Type'} : (term35 A) = (term83 A).
Proof. exact (TRANS (@lem7607431 A) (@lem7607458 A)). Qed.
Lemma lem7607566 {A : Type'} : (term4 A) = (term83 A).
Proof. exact (TRANS (@lem7607301 A) (@lem7607565 A)). Qed.
Lemma lem7607567 {A : Type'} (h1 : term4 A) : term83 A.
Proof. exact (EQ_MP (@lem7607566 A) (@lem7607263 A h1)). Qed.
Lemma lem7607568 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7607569 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7607568 A s)). Qed.
Lemma lem7607570 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7607579 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7607570 A) (@lem7607569 A)). Qed.
Lemma lem7607580 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (EQ_MP (@lem7607579 A) (@lem7607264 A h1)). Qed.
Lemma lem7607586 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7607609 {A : Type'} (s : type33 A) (n : nat) : (term24 A s n) = (term24 A s n).
Proof. exact (eq_refl (term24 A s n)). Qed.
Lemma lem7607610 {A : Type'} (s : type33 A) : (term43 A s) = (term43 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607609 A s n)). Qed.
Lemma lem7607611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607612 {A : Type'} (s : type33 A) : (term58 A s) = (term58 A s).
Proof. exact (MK_COMB (@lem7607611) (@lem7607610 A s)). Qed.
Lemma lem7607613 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607612 A s)). Qed.
Lemma lem7607614 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607615 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (MK_COMB (@lem7607614 A) (@lem7607613 A)). Qed.
Lemma lem7607640 {A : Type'} (s : type33 A) (n : nat) : (term27 A s n) = (term27 A s n).
Proof. exact (eq_refl (term27 A s n)). Qed.
Lemma lem7607641 {A : Type'} (s : type33 A) : (term42 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607640 A s n)). Qed.
Lemma lem7607642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607643 {A : Type'} (s : type33 A) : (term53 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem7607642) (@lem7607641 A s)). Qed.
Lemma lem7607644 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607643 A s)). Qed.
Lemma lem7607645 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607646 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (MK_COMB (@lem7607645 A) (@lem7607644 A)). Qed.
Lemma lem7607647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7607648 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (MK_COMB (@lem7607647) (@lem7607646 A)). Qed.
Lemma lem7607649 {A : Type'} : (term83 A) = (term83 A).
Proof. exact (MK_COMB (@lem7607648 A) (@lem7607615 A)). Qed.
Lemma lem7607650 {A : Type'} (h1 : term4 A) : term83 A.
Proof. exact (EQ_MP (@lem7607649 A) (@lem7607567 A h1)). Qed.
Lemma lem7607657 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7607658 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7607657 A s)). Qed.
Lemma lem7607659 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7607660 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7607659 A) (@lem7607658 A)). Qed.
Lemma lem7607661 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (EQ_MP (@lem7607660 A) (@lem7607580 A h1)). Qed.
Lemma lem7607662 {A : Type'} (h1 : term4 A) : term82 A.
Proof. exact (proj2 (@lem7607650 A h1)). Qed.
Lemma lem7607667 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7607669 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7607670 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7607669 A s)). Qed.
Lemma lem7607671 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7607673 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7607671 A) (@lem7607670 A)). Qed.
Lemma lem7607674 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (EQ_MP (@lem7607673 A) (@lem7607661 A h1)). Qed.
Lemma lem7607714 {A : Type'} (s : type33 A) (n : nat) : (term24 A s n) = (term84 A s n).
Proof. exact (@lem19490 (@FINITE (finite_image A) s) (term85 A s n) ((@CARD (finite_image A) s) = n)). Qed.
Lemma lem7607715 {A : Type'} (s : type33 A) : (term43 A s) = (term86 A s).
Proof. exact (fun_ext (fun n : nat => @lem7607714 A s n)). Qed.
Lemma lem7607716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7607717 {A : Type'} (s : type33 A) : (term58 A s) = (term87 A s).
Proof. exact (MK_COMB (@lem7607716) (@lem7607715 A s)). Qed.
Lemma lem7607718 {A : Type'} : (term67 A) = (term88 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7607717 A s)). Qed.
Lemma lem7607719 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7607721 {A : Type'} : (term82 A) = (term89 A).
Proof. exact (MK_COMB (@lem7607719 A) (@lem7607718 A)). Qed.
Lemma lem7607722 {A : Type'} (h1 : term4 A) : term89 A.
Proof. exact (EQ_MP (@lem7607721 A) (@lem7607662 A h1)). Qed.
Lemma lem7607723 {A : Type'} (_97836 : A -> Prop) (h1 : term3 A) : term90 A _97836.
Proof. exact (@lem7607674 A h1 _97836). Qed.
Lemma lem7607724 {A : Type'} (_97836 : A -> Prop) : (term90 A _97836) = (term16 A _97836).
Proof. exact (eq_refl (term90 A _97836)). Qed.
Lemma lem7607732 {A : Type'} (_97839 : type33 A) (h1 : term4 A) : term91 A _97839.
Proof. exact (@lem7607722 A h1 _97839). Qed.
Lemma lem7607733 {A : Type'} (_97839 : type33 A) : (term91 A _97839) = (term87 A _97839).
Proof. exact (eq_refl (term91 A _97839)). Qed.
Lemma lem7607734 {A : Type'} (_97839 : type33 A) (h1 : term4 A) : term87 A _97839.
Proof. exact (EQ_MP (@lem7607733 A _97839) (@lem7607732 A _97839 h1)). Qed.
Lemma lem7607735 {A : Type'} (_97839 : type33 A) (_97840 : nat) (h1 : term4 A) : term92 A _97839 _97840.
Proof. exact (@lem7607734 A _97839 h1 _97840). Qed.
Lemma lem7607736 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term92 A _97839 _97840) = (term84 A _97839 _97840).
Proof. exact (eq_refl (term92 A _97839 _97840)). Qed.
Lemma lem7607737 {A : Type'} (_97839 : type33 A) (_97840 : nat) (h1 : term4 A) : term84 A _97839 _97840.
Proof. exact (EQ_MP (@lem7607736 A _97839 _97840) (@lem7607735 A _97839 _97840 h1)). Qed.
Lemma lem7607741 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7607759 {A : Type'} (_97840 : nat) (_97839 : type33 A) (h1 : term4 A) : term93 A _97840 _97839.
Proof. exact (proj1 (@lem7607737 A _97839 _97840 h1)). Qed.
Lemma lem7607820 {A : Type'} (_97836 : A -> Prop) (h1 : term3 A) : term16 A _97836.
Proof. exact (EQ_MP (@lem7607724 A _97836) (@lem7607723 A _97836 h1)). Qed.
Lemma lem7607821 {A : Type'} (_97836 : A -> Prop) (h1 : term3 A) : term16 A _97836.
Proof. exact (@lem7607820 A _97836 h1). Qed.
Lemma lem7607822 {A : Type'} (_97851 : A -> Prop) (h1 : term3 A) : term16 A _97851.
Proof. exact (@lem7607821 A _97851 h1). Qed.
Lemma lem7607823 {A : Type'} (_97851 : A -> Prop) (h1 : term3 A) : term94 A _97851.
Proof. exact (fun h0 : term95 A _97851 => @lem7607822 A _97851 h1). Qed.
Lemma lem7607825 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607826 {A : Type'} (_97851 : A -> Prop) : (term94 A _97851) = (term16 A _97851).
Proof. exact (@lem7607825 (term16 A _97851)). Qed.
Lemma lem7607827 {A : Type'} (_97851 : A -> Prop) (h1 : term3 A) : term16 A _97851.
Proof. exact (EQ_MP (@lem7607826 A _97851) (@lem7607823 A _97851 h1)). Qed.
Lemma lem7607833 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7607834 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term93 A _97840 _97839) = (term97 A _97839 _97840).
Proof. exact (@lem7607833 (@FINITE (finite_image A) _97839) (term85 A _97839 _97840)). Qed.
Lemma lem7607840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7607841 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term98 A _97840 _97839) = (term99 A _97839 _97840).
Proof. exact (MK_COMB (@lem7607840) (@lem7607834 A _97839 _97840)). Qed.
Lemma lem7607847 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term97 A _97839 _97840) = (term97 A _97839 _97840).
Proof. exact (eq_refl (term97 A _97839 _97840)). Qed.
Lemma lem7607848 {A : Type'} (_97839 : type33 A) (_97840 : nat) : ((term93 A _97840 _97839) = (term97 A _97839 _97840)) = ((term97 A _97839 _97840) = (term97 A _97839 _97840)).
Proof. exact (MK_COMB (@lem7607841 A _97839 _97840) (@lem7607847 A _97839 _97840)). Qed.
Lemma lem7607850 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7607851 (x : Prop) : (x = x) = True.
Proof. exact (@lem7607850 Prop x). Qed.
Lemma lem7607852 {A : Type'} (_97839 : type33 A) (_97840 : nat) : ((term97 A _97839 _97840) = (term97 A _97839 _97840)) = True.
Proof. exact (@lem7607851 (term97 A _97839 _97840)). Qed.
Lemma lem7607853 {A : Type'} (_97839 : type33 A) (_97840 : nat) : ((term93 A _97840 _97839) = (term97 A _97839 _97840)) = True.
Proof. exact (TRANS (@lem7607848 A _97839 _97840) (@lem7607852 A _97839 _97840)). Qed.
Lemma lem7607854 {A : Type'} (_97839 : type33 A) (_97840 : nat) : True = ((term93 A _97840 _97839) = (term97 A _97839 _97840)).
Proof. exact (SYM (@lem7607853 A _97839 _97840)). Qed.
Lemma lem7607855 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term93 A _97840 _97839) = (term97 A _97839 _97840).
Proof. exact (EQ_MP (@lem7607854 A _97839 _97840) (@lem0)). Qed.
Lemma lem7607856 {A : Type'} (_97839 : type33 A) (_97840 : nat) (h1 : term4 A) : term97 A _97839 _97840.
Proof. exact (EQ_MP (@lem7607855 A _97839 _97840) (@lem7607759 A _97840 _97839 h1)). Qed.
Lemma lem7607858 (b : Prop) (a : Prop) : (a \/ b) = (term100 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7607859 {A : Type'} (_97840 : nat) (_97839 : type33 A) : (term97 A _97839 _97840) = (term101 A _97840 _97839).
Proof. exact (@lem7607858 (term85 A _97839 _97840) (@FINITE (finite_image A) _97839)). Qed.
Lemma lem7607861 (a : Prop) : (term102 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7607862 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term103 A _97839 _97840) = (@HAS_SIZE (finite_image A) _97839 _97840).
Proof. exact (@lem7607861 (@HAS_SIZE (finite_image A) _97839 _97840)). Qed.
Lemma lem7607863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7607864 {A : Type'} (_97839 : type33 A) (_97840 : nat) : (term104 A _97839 _97840) = (term105 A _97839 _97840).
Proof. exact (MK_COMB (@lem7607863) (@lem7607862 A _97839 _97840)). Qed.
Lemma lem7607865 {A : Type'} (_97839 : type33 A) : (@FINITE (finite_image A) _97839) = (@FINITE (finite_image A) _97839).
Proof. exact (eq_refl (@FINITE (finite_image A) _97839)). Qed.
Lemma lem7607866 {A : Type'} (_97840 : nat) (_97839 : type33 A) : (term101 A _97840 _97839) = (term106 A _97840 _97839).
Proof. exact (MK_COMB (@lem7607864 A _97839 _97840) (@lem7607865 A _97839)). Qed.
Lemma lem7607867 {A : Type'} (_97840 : nat) (_97839 : type33 A) : (term97 A _97839 _97840) = (term106 A _97840 _97839).
Proof. exact (TRANS (@lem7607859 A _97840 _97839) (@lem7607866 A _97840 _97839)). Qed.
Lemma lem7607870 {A : Type'} (_97840 : nat) (_97839 : type33 A) (h1 : term4 A) : term106 A _97840 _97839.
Proof. exact (EQ_MP (@lem7607867 A _97840 _97839) (@lem7607856 A _97839 _97840 h1)). Qed.
Lemma lem7607871 {A : Type'} (_97840 : nat) (_97839 : type33 A) (h1 : term4 A) : term106 A _97840 _97839.
Proof. exact (@lem7607870 A _97840 _97839 h1). Qed.
Lemma lem7607872 {A : Type'} (_97851 : A -> Prop) (h1 : term4 A) : term107 A _97851.
Proof. exact (@lem7607871 A (@dimindex A _97851) (@UNIV (finite_image A)) h1). Qed.
Lemma lem7607875 {A : Type'} (h1 : term3 A) (h2 : term4 A) : @FINITE (finite_image A) (@UNIV (finite_image A)).
Proof. exact (@lem7607872 A (@el (A -> Prop)) h2 (@lem7607827 A (@el (A -> Prop)) h1)). Qed.
Lemma lem7607876 {A : Type'} (h1 : term3 A) (h2 : term4 A) : term108 A.
Proof. exact (fun h0 : term2 A => @lem7607875 A h1 h2). Qed.
Lemma lem7607878 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607879 {A : Type'} : (term108 A) = (@FINITE (finite_image A) (@UNIV (finite_image A))).
Proof. exact (@lem7607878 (@FINITE (finite_image A) (@UNIV (finite_image A)))). Qed.
Lemma lem7607880 {A : Type'} (h1 : term3 A) (h2 : term4 A) : @FINITE (finite_image A) (@UNIV (finite_image A)).
Proof. exact (EQ_MP (@lem7607879 A) (@lem7607876 A h1 h2)). Qed.
Lemma lem7607883 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7607885 {A : Type'} : (term2 A) = (term109 A).
Proof. exact (@lem7607883 (@FINITE (finite_image A) (@UNIV (finite_image A)))). Qed.
Lemma lem7607888 {A : Type'} (h1 : term2 A) : term109 A.
Proof. exact (EQ_MP (@lem7607885 A) (@lem7607741 A h1)). Qed.
Lemma lem7607891 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (@lem7607888 A h3 (@lem7607880 A h1 h2)). Qed.
Lemma lem7607892 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : term110.
Proof. exact (fun h0 : ~ False => @lem7607891 A h1 h2 h3). Qed.
Lemma lem7607894 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7607895 : term110 = False.
Proof. exact (@lem7607894 False). Qed.
Lemma lem7607896 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607895) (@lem7607892 A h1 h2 h3)). Qed.
Lemma lem7607897 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7607896 A h1 h2 h3) (fun h4 : False => @lem7607741 A h3)). Qed.
Lemma lem7607898 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607897 A h1 h2 h3) (@lem7607741 A h3)). Qed.
Lemma lem7607899 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7607898 A h1 h2 h3) (fun h4 : False => @lem7607667 A h3)). Qed.
Lemma lem7607900 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607899 A h1 h2 h3) (@lem7607667 A h3)). Qed.
Lemma lem7607901 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7607900 A h1 h2 h3) (fun h4 : False => @lem7607674 A h1)). Qed.
Lemma lem7607902 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607901 A h1 h2 h3) (@lem7607674 A h1)). Qed.
Lemma lem7607903 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7607902 A h1 h2 h3) (fun h4 : False => @lem7607667 A h3)). Qed.
Lemma lem7607904 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607903 A h1 h2 h3) (@lem7607667 A h3)). Qed.
Lemma lem7607905 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7607904 A h1 h2 h3) (fun h4 : False => @lem7607661 A h1)). Qed.
Lemma lem7607906 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607905 A h1 h2 h3) (@lem7607661 A h1)). Qed.
Lemma lem7607907 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7607906 A h1 h2 h3) (fun h4 : False => @lem7607586 A h3)). Qed.
Lemma lem7607908 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607907 A h1 h2 h3) (@lem7607586 A h3)). Qed.
Lemma lem7607909 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7607908 A h1 h2 h3) (fun h4 : False => @lem7607580 A h1)). Qed.
Lemma lem7607910 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607909 A h1 h2 h3) (@lem7607580 A h1)). Qed.
Lemma lem7607911 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7607910 A h1 h2 h3) (fun h4 : False => @lem7607270 A h3)). Qed.
Lemma lem7607912 {A : Type'} (h1 : term3 A) (h2 : term4 A) (h3 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607911 A h1 h2 h3) (@lem7607270 A h3)). Qed.
Lemma lem7607913 {A : Type'} (h1 : term4 A) (h2 : term2 A) : term9 A.
Proof. exact (fun h0 : term3 A => @lem7607912 A h0 h1 h2). Qed.
Lemma lem7607914 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term3 A)). Qed.
Lemma lem7607915 {A : Type'} (h1 : term4 A) (h2 : term2 A) : term10 A.
Proof. exact (EQ_MP (@lem7607914 A) (@lem7607913 A h1 h2)). Qed.
Lemma lem7607916 {A : Type'} (h1 : term2 A) : term13 A.
Proof. exact (fun h0 : term4 A => @lem7607915 A h0 h1). Qed.
Lemma lem7607917 {A : Type'} : term15 A.
Proof. exact (fun h0 : term2 A => @lem7607916 A h0). Qed.
Lemma lem7607918 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem7607261 A) (@lem7607917 A)). Qed.
Lemma lem7607920 {A : Type'} : term5 A.
Proof. exact (@lem7607170 A (@lem7607918 A)). Qed.
Lemma lem7607921 {A : Type'} (h1 : term2 A) : term12 A.
Proof. exact (@lem7607920 A (@lem7607151 A h1)). Qed.
Lemma lem7607922 {A : Type'} (h1 : term2 A) : term9 A.
Proof. exact (@lem7607921 A h1 (@lem7607153 A)). Qed.
Lemma lem7607923 {A : Type'} (h1 : term2 A) : False.
Proof. exact (@lem7607922 A h1 (@lem7607152 A)). Qed.
Lemma lem7607924 {A : Type'} (h1 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h2 : term2 A => @lem7607923 A h1) (fun h2 : False => @lem7607151 A h1)). Qed.
Lemma lem7607925 {A : Type'} (h1 : term2 A) : False.
Proof. exact (EQ_MP (@lem7607924 A h1) (@lem7607151 A h1)). Qed.
Lemma lem7607926 {A : Type'} : term1 A.
Proof. exact (fun h0 : term2 A => @lem7607925 A h0). Qed.
Lemma lem7607927 {A : Type'} : @FINITE (finite_image A) (@UNIV (finite_image A)).
Proof. exact (EQ_MP (@lem7607150 A) (@lem7607926 A)). Qed.
