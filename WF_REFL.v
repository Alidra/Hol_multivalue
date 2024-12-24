Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REFL_term_abbrevs.
Require Import WF_ANTISYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem368307 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem368308 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term2 A lt2).
Proof. exact (@lem368307 (term1 A lt2)). Qed.
Lemma lem368309 {A : Type'} (lt2 : type1402 A) : (term2 A lt2) = (term1 A lt2).
Proof. exact (SYM (@lem368308 A lt2)). Qed.
Lemma lem368310 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term3 A lt2.
Proof. exact (h1). Qed.
Lemma lem368311 {A : Type'} : term4 A.
Proof. exact (@lem368295 A). Qed.
Lemma lem368314 {A : Type'} (lt2 : type1402 A) (h1 : term5 A lt2) : term5 A lt2.
Proof. exact (h1). Qed.
Lemma lem368315 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (fun h0 : term5 A lt2 => @lem368314 A lt2 h0). Qed.
Lemma lem368316 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term6 A lt2.
Proof. exact (h1). Qed.
Lemma lem368317 {A : Type'} (lt2 : type1402 A) (h1 : term5 A lt2) : term5 A lt2.
Proof. exact (h1). Qed.
Lemma lem368318 {A : Type'} (lt2 : type1402 A) (h1 : term5 A lt2) (h2 : term6 A lt2) : term5 A lt2.
Proof. exact (@lem368316 A lt2 h2 (@lem368317 A lt2 h1)). Qed.
Lemma lem368319 {A : Type'} (lt2 : type1402 A) (h1 : term5 A lt2) : term7 A lt2.
Proof. exact (fun h0 : term6 A lt2 => @lem368318 A lt2 h1 h0). Qed.
Lemma lem368320 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term6 A lt2.
Proof. exact (h1). Qed.
Lemma lem368321 {A : Type'} (lt2 : type1402 A) (h1 : term5 A lt2) (h2 : term6 A lt2) : term5 A lt2.
Proof. exact (@lem368319 A lt2 h1 (@lem368320 A lt2 h2)). Qed.
Lemma lem368322 {A : Type'} (lt2 : type1402 A) (h1 : term6 A lt2) : term6 A lt2.
Proof. exact (fun h0 : term5 A lt2 => @lem368321 A lt2 h0 h1). Qed.
Lemma lem368323 {A : Type'} (lt2 : type1402 A) : term8 A lt2.
Proof. exact (fun h0 : term6 A lt2 => @lem368322 A lt2 h0). Qed.
Lemma lem368326 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (@lem368323 A lt2 (@lem368315 A lt2)). Qed.
Lemma lem368327 {A : Type'} (lt2 : type1402 A) : term6 A lt2.
Proof. exact (@lem368326 A lt2). Qed.
Lemma lem368341 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem368342 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem368341 (term4 A)). Qed.
Lemma lem368359 {A : Type'} (lt2 : type1402 A) : (term11 A lt2) = (term11 A lt2).
Proof. exact (eq_refl (term11 A lt2)). Qed.
Lemma lem368360 {A : Type'} (lt2 : type1402 A) : (term5 A lt2) = (term12 A lt2).
Proof. exact (MK_COMB (@lem368359 A lt2) (@lem368342 A)). Qed.
Lemma lem368363 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368360 A lt2)). Qed.
Lemma lem368364 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368373 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem368364 A) (@lem368363 A)). Qed.
Lemma lem368384 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term17 A lt2 y x).
Proof. exact (eq_refl (term17 A lt2 y x)). Qed.
Lemma lem368385 {A : Type'} (lt2 : type1402 A) (x : A) : (term18 A lt2 x) = (term18 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368384 A lt2 y x)). Qed.
Lemma lem368386 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368387 {A : Type'} (lt2 : type1402 A) (x : A) : (term19 A lt2 x) = (term19 A lt2 x).
Proof. exact (MK_COMB (@lem368386 A) (@lem368385 A lt2 x)). Qed.
Lemma lem368388 {A : Type'} (lt2 : type1402 A) : (term20 A lt2) = (term20 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368387 A lt2 x)). Qed.
Lemma lem368389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368390 {A : Type'} (lt2 : type1402 A) : (term21 A lt2) = (term21 A lt2).
Proof. exact (MK_COMB (@lem368389 A) (@lem368388 A lt2)). Qed.
Lemma lem368391 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368390 A lt2)). Qed.
Lemma lem368392 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368393 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem368392 A) (@lem368391 A)). Qed.
Lemma lem368394 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368395 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem368394) (@lem368393 A)). Qed.
Lemma lem368402 {A : Type'} (lt2 : type1402 A) (x : A) : (term23 A lt2 x) = (term23 A lt2 x).
Proof. exact (eq_refl (term23 A lt2 x)). Qed.
Lemma lem368403 {A : Type'} (lt2 : type1402 A) : (term24 A lt2) = (term24 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368402 A lt2 x)). Qed.
Lemma lem368404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368405 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term1 A lt2).
Proof. exact (MK_COMB (@lem368404 A) (@lem368403 A lt2)). Qed.
Lemma lem368406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368407 {A : Type'} (lt2 : type1402 A) : (term3 A lt2) = (term3 A lt2).
Proof. exact (MK_COMB (@lem368406) (@lem368405 A lt2)). Qed.
Lemma lem368408 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem368409 {A : Type'} (lt2 : type1402 A) : (term11 A lt2) = (term11 A lt2).
Proof. exact (MK_COMB (@lem368408) (@lem368407 A lt2)). Qed.
Lemma lem368410 {A : Type'} (lt2 : type1402 A) : (term12 A lt2) = (term12 A lt2).
Proof. exact (MK_COMB (@lem368409 A lt2) (@lem368395 A)). Qed.
Lemma lem368411 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368410 A lt2)). Qed.
Lemma lem368412 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368413 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem368412 A) (@lem368411 A)). Qed.
Lemma lem368454 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (TRANS (@lem368373 A) (@lem368413 A)). Qed.
Lemma lem368455 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem368454 A)). Qed.
Lemma lem368456 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term3 A lt2.
Proof. exact (h1). Qed.
Lemma lem368457 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem368461 {A : Type'} (lt2 : type1402 A) (x : A) : (term25 A lt2 x) = (lt2 x x).
Proof. exact (@lem16933 (lt2 x x)). Qed.
Lemma lem368463 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term26 A lt2).
Proof. exact (eq_refl (term26 A lt2)). Qed.
Lemma lem368464 {A : Type'} (lt2 : type1402 A) (x : A) : (term27 A lt2 x) = (term28 A lt2 x).
Proof. exact (MK_COMB (@lem368463 A lt2) (@lem368461 A lt2 x)). Qed.
Lemma lem368465 {A : Type'} (lt2 : type1402 A) (x : A) : (term29 A lt2 x) = (term27 A lt2 x).
Proof. exact (@lem17362 (@WF A lt2) (term30 A lt2 x)). Qed.
Lemma lem368466 {A : Type'} (lt2 : type1402 A) (x : A) : (term29 A lt2 x) = (term28 A lt2 x).
Proof. exact (TRANS (@lem368465 A lt2 x) (@lem368464 A lt2 x)). Qed.
Lemma lem368467 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem368468 {A : Type'} (lt2 : type1402 A) : (term3 A lt2) = (term33 A lt2).
Proof. exact (@lem368467 A (term24 A lt2)). Qed.
Lemma lem368469 {A : Type'} (lt2 : type1402 A) (x : A) : (term34 A lt2 x) = (term23 A lt2 x).
Proof. exact (eq_refl (term34 A lt2 x)). Qed.
Lemma lem368470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368471 {A : Type'} (lt2 : type1402 A) (x : A) : (term35 A lt2 x) = (term29 A lt2 x).
Proof. exact (MK_COMB (@lem368470) (@lem368469 A lt2 x)). Qed.
Lemma lem368472 {A : Type'} (lt2 : type1402 A) (x : A) : (term35 A lt2 x) = (term28 A lt2 x).
Proof. exact (TRANS (@lem368471 A lt2 x) (@lem368466 A lt2 x)). Qed.
Lemma lem368473 {A : Type'} (lt2 : type1402 A) : (term36 A lt2) = (term37 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368472 A lt2 x)). Qed.
Lemma lem368474 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem368475 {A : Type'} (lt2 : type1402 A) : (term33 A lt2) = (term38 A lt2).
Proof. exact (MK_COMB (@lem368474 A) (@lem368473 A lt2)). Qed.
Lemma lem368476 {A : Type'} (lt2 : type1402 A) : (term3 A lt2) = (term38 A lt2).
Proof. exact (TRANS (@lem368468 A lt2) (@lem368475 A lt2)). Qed.
Lemma lem368478 {A : Type'} (P : Prop) (Q : A -> Prop) : (term39 A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem368479 {A : Type'} (P : Prop) (Q : A -> Prop) : (term39 A P Q) = (term40 A P Q).
Proof. exact (@lem368478 A P Q). Qed.
Lemma lem368480 {A : Type'} (lt2 : type1402 A) : (term41 A lt2) = (term42 A lt2).
Proof. exact (@lem368479 A (@WF A lt2) (term43 A lt2)). Qed.
Lemma lem368481 {A : Type'} (lt2 : type1402 A) (x : A) : (term44 A lt2 x) = (lt2 x x).
Proof. exact (eq_refl (term44 A lt2 x)). Qed.
Lemma lem368482 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term26 A lt2).
Proof. exact (eq_refl (term26 A lt2)). Qed.
Lemma lem368483 {A : Type'} (lt2 : type1402 A) (x : A) : (term45 A lt2 x) = (term28 A lt2 x).
Proof. exact (MK_COMB (@lem368482 A lt2) (@lem368481 A lt2 x)). Qed.
Lemma lem368484 {A : Type'} (lt2 : type1402 A) : (term46 A lt2) = (term37 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368483 A lt2 x)). Qed.
Lemma lem368485 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem368486 {A : Type'} (lt2 : type1402 A) : (term41 A lt2) = (term38 A lt2).
Proof. exact (MK_COMB (@lem368485 A) (@lem368484 A lt2)). Qed.
Lemma lem368487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368488 {A : Type'} (lt2 : type1402 A) : (term47 A lt2) = (term48 A lt2).
Proof. exact (MK_COMB (@lem368487) (@lem368486 A lt2)). Qed.
Lemma lem368489 {A : Type'} (lt2 : type1402 A) (x : A) : (term44 A lt2 x) = (lt2 x x).
Proof. exact (eq_refl (term44 A lt2 x)). Qed.
Lemma lem368490 {A : Type'} (lt2 : type1402 A) : (term49 A lt2) = (term43 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368489 A lt2 x)). Qed.
Lemma lem368491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem368492 {A : Type'} (lt2 : type1402 A) : (term50 A lt2) = (term51 A lt2).
Proof. exact (MK_COMB (@lem368491 A) (@lem368490 A lt2)). Qed.
Lemma lem368493 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term26 A lt2).
Proof. exact (eq_refl (term26 A lt2)). Qed.
Lemma lem368494 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term52 A lt2).
Proof. exact (MK_COMB (@lem368493 A lt2) (@lem368492 A lt2)). Qed.
Lemma lem368495 {A : Type'} (lt2 : type1402 A) : ((term41 A lt2) = (term42 A lt2)) = ((term38 A lt2) = (term52 A lt2)).
Proof. exact (MK_COMB (@lem368488 A lt2) (@lem368494 A lt2)). Qed.
Lemma lem368496 {A : Type'} (lt2 : type1402 A) : (term38 A lt2) = (term52 A lt2).
Proof. exact (EQ_MP (@lem368495 A lt2) (@lem368480 A lt2)). Qed.
Lemma lem368502 {A : Type'} (P : Prop) (Q : A -> Prop) : (term40 A P Q) = (term39 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem368503 {A : Type'} (P : Prop) (Q : A -> Prop) : (term40 A P Q) = (term39 A P Q).
Proof. exact (@lem368502 A P Q). Qed.
Lemma lem368504 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term41 A lt2).
Proof. exact (@lem368503 A (@WF A lt2) (term43 A lt2)). Qed.
Lemma lem368505 {A : Type'} (lt2 : type1402 A) (x : A) : (term44 A lt2 x) = (lt2 x x).
Proof. exact (eq_refl (term44 A lt2 x)). Qed.
Lemma lem368506 {A : Type'} (lt2 : type1402 A) : (term49 A lt2) = (term43 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368505 A lt2 x)). Qed.
Lemma lem368507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem368508 {A : Type'} (lt2 : type1402 A) : (term50 A lt2) = (term51 A lt2).
Proof. exact (MK_COMB (@lem368507 A) (@lem368506 A lt2)). Qed.
Lemma lem368509 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term26 A lt2).
Proof. exact (eq_refl (term26 A lt2)). Qed.
Lemma lem368510 {A : Type'} (lt2 : type1402 A) : (term42 A lt2) = (term52 A lt2).
Proof. exact (MK_COMB (@lem368509 A lt2) (@lem368508 A lt2)). Qed.
Lemma lem368511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368512 {A : Type'} (lt2 : type1402 A) : (term53 A lt2) = (term54 A lt2).
Proof. exact (MK_COMB (@lem368511) (@lem368510 A lt2)). Qed.
Lemma lem368513 {A : Type'} (lt2 : type1402 A) (x : A) : (term44 A lt2 x) = (lt2 x x).
Proof. exact (eq_refl (term44 A lt2 x)). Qed.
Lemma lem368514 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term26 A lt2).
Proof. exact (eq_refl (term26 A lt2)). Qed.
Lemma lem368515 {A : Type'} (lt2 : type1402 A) (x : A) : (term45 A lt2 x) = (term28 A lt2 x).
Proof. exact (MK_COMB (@lem368514 A lt2) (@lem368513 A lt2 x)). Qed.
Lemma lem368516 {A : Type'} (lt2 : type1402 A) : (term46 A lt2) = (term37 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368515 A lt2 x)). Qed.
Lemma lem368517 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem368518 {A : Type'} (lt2 : type1402 A) : (term41 A lt2) = (term38 A lt2).
Proof. exact (MK_COMB (@lem368517 A) (@lem368516 A lt2)). Qed.
Lemma lem368519 {A : Type'} (lt2 : type1402 A) : ((term42 A lt2) = (term41 A lt2)) = ((term52 A lt2) = (term38 A lt2)).
Proof. exact (MK_COMB (@lem368512 A lt2) (@lem368518 A lt2)). Qed.
Lemma lem368520 {A : Type'} (lt2 : type1402 A) : (term52 A lt2) = (term38 A lt2).
Proof. exact (EQ_MP (@lem368519 A lt2) (@lem368504 A lt2)). Qed.
Lemma lem368521 {A : Type'} (lt2 : type1402 A) : (term38 A lt2) = (term38 A lt2).
Proof. exact (TRANS (@lem368496 A lt2) (@lem368520 A lt2)). Qed.
Lemma lem368522 {A : Type'} (lt2 : type1402 A) : (term3 A lt2) = (term38 A lt2).
Proof. exact (TRANS (@lem368476 A lt2) (@lem368521 A lt2)). Qed.
Lemma lem368523 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term38 A lt2.
Proof. exact (EQ_MP (@lem368522 A lt2) (@lem368456 A lt2 h1)). Qed.
Lemma lem368531 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term55 A lt2 y x) = (term56 A lt2 y x).
Proof. exact (@lem17045 (lt2 x y) (lt2 y x)). Qed.
Lemma lem368533 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term57 A lt2).
Proof. exact (eq_refl (term57 A lt2)). Qed.
Lemma lem368534 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term58 A lt2 y x) = (term59 A lt2 y x).
Proof. exact (MK_COMB (@lem368533 A lt2) (@lem368531 A lt2 y x)). Qed.
Lemma lem368535 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term58 A lt2 y x).
Proof. exact (@lem17265 (@WF A lt2) (term55 A lt2 y x)). Qed.
Lemma lem368536 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term59 A lt2 y x).
Proof. exact (TRANS (@lem368535 A lt2 y x) (@lem368534 A lt2 y x)). Qed.
Lemma lem368537 {A : Type'} (lt2 : type1402 A) (x : A) : (term18 A lt2 x) = (term60 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368536 A lt2 y x)). Qed.
Lemma lem368538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368539 {A : Type'} (lt2 : type1402 A) (x : A) : (term19 A lt2 x) = (term61 A lt2 x).
Proof. exact (MK_COMB (@lem368538 A) (@lem368537 A lt2 x)). Qed.
Lemma lem368540 {A : Type'} (lt2 : type1402 A) : (term20 A lt2) = (term62 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368539 A lt2 x)). Qed.
Lemma lem368541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368542 {A : Type'} (lt2 : type1402 A) : (term21 A lt2) = (term63 A lt2).
Proof. exact (MK_COMB (@lem368541 A) (@lem368540 A lt2)). Qed.
Lemma lem368543 {A : Type'} : (term22 A) = (term64 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368542 A lt2)). Qed.
Lemma lem368544 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368545 {A : Type'} : (term4 A) = (term65 A).
Proof. exact (MK_COMB (@lem368544 A) (@lem368543 A)). Qed.
Lemma lem368555 {A : Type'} (P : Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem368556 {A : Type'} (P : Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (@lem368555 A P Q). Qed.
Lemma lem368557 {A : Type'} (lt2 : type1402 A) (x : A) : (term68 A lt2 x) = (term69 A lt2 x).
Proof. exact (@lem368556 A (term70 A lt2) (term71 A lt2 x)). Qed.
Lemma lem368558 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term72 A lt2 x y) = (term56 A lt2 y x).
Proof. exact (eq_refl (term72 A lt2 x y)). Qed.
Lemma lem368559 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term57 A lt2).
Proof. exact (eq_refl (term57 A lt2)). Qed.
Lemma lem368560 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term73 A lt2 x y) = (term59 A lt2 y x).
Proof. exact (MK_COMB (@lem368559 A lt2) (@lem368558 A lt2 y x)). Qed.
Lemma lem368561 {A : Type'} (lt2 : type1402 A) (x : A) : (term74 A lt2 x) = (term60 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368560 A lt2 y x)). Qed.
Lemma lem368562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368563 {A : Type'} (lt2 : type1402 A) (x : A) : (term68 A lt2 x) = (term61 A lt2 x).
Proof. exact (MK_COMB (@lem368562 A) (@lem368561 A lt2 x)). Qed.
Lemma lem368564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368565 {A : Type'} (lt2 : type1402 A) (x : A) : (term75 A lt2 x) = (term76 A lt2 x).
Proof. exact (MK_COMB (@lem368564) (@lem368563 A lt2 x)). Qed.
Lemma lem368566 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term72 A lt2 x y) = (term56 A lt2 y x).
Proof. exact (eq_refl (term72 A lt2 x y)). Qed.
Lemma lem368567 {A : Type'} (lt2 : type1402 A) (x : A) : (term77 A lt2 x) = (term71 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368566 A lt2 y x)). Qed.
Lemma lem368568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368569 {A : Type'} (lt2 : type1402 A) (x : A) : (term78 A lt2 x) = (term79 A lt2 x).
Proof. exact (MK_COMB (@lem368568 A) (@lem368567 A lt2 x)). Qed.
Lemma lem368570 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term57 A lt2).
Proof. exact (eq_refl (term57 A lt2)). Qed.
Lemma lem368571 {A : Type'} (lt2 : type1402 A) (x : A) : (term69 A lt2 x) = (term80 A lt2 x).
Proof. exact (MK_COMB (@lem368570 A lt2) (@lem368569 A lt2 x)). Qed.
Lemma lem368572 {A : Type'} (lt2 : type1402 A) (x : A) : ((term68 A lt2 x) = (term69 A lt2 x)) = ((term61 A lt2 x) = (term80 A lt2 x)).
Proof. exact (MK_COMB (@lem368565 A lt2 x) (@lem368571 A lt2 x)). Qed.
Lemma lem368573 {A : Type'} (lt2 : type1402 A) (x : A) : (term61 A lt2 x) = (term80 A lt2 x).
Proof. exact (EQ_MP (@lem368572 A lt2 x) (@lem368557 A lt2 x)). Qed.
Lemma lem368622 {A : Type'} (lt2 : type1402 A) : (term62 A lt2) = (term81 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368573 A lt2 x)). Qed.
Lemma lem368623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368624 {A : Type'} (lt2 : type1402 A) : (term63 A lt2) = (term82 A lt2).
Proof. exact (MK_COMB (@lem368623 A) (@lem368622 A lt2)). Qed.
Lemma lem368626 {A : Type'} (P : Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem368627 {A : Type'} (P : Prop) (Q : A -> Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (@lem368626 A P Q). Qed.
Lemma lem368628 {A : Type'} (lt2 : type1402 A) : (term83 A lt2) = (term84 A lt2).
Proof. exact (@lem368627 A (term70 A lt2) (term85 A lt2)). Qed.
Lemma lem368629 {A : Type'} (lt2 : type1402 A) (x : A) : (term86 A lt2 x) = (term79 A lt2 x).
Proof. exact (eq_refl (term86 A lt2 x)). Qed.
Lemma lem368630 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term57 A lt2).
Proof. exact (eq_refl (term57 A lt2)). Qed.
Lemma lem368631 {A : Type'} (lt2 : type1402 A) (x : A) : (term87 A lt2 x) = (term80 A lt2 x).
Proof. exact (MK_COMB (@lem368630 A lt2) (@lem368629 A lt2 x)). Qed.
Lemma lem368632 {A : Type'} (lt2 : type1402 A) : (term88 A lt2) = (term81 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368631 A lt2 x)). Qed.
Lemma lem368633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368634 {A : Type'} (lt2 : type1402 A) : (term83 A lt2) = (term82 A lt2).
Proof. exact (MK_COMB (@lem368633 A) (@lem368632 A lt2)). Qed.
Lemma lem368635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368636 {A : Type'} (lt2 : type1402 A) : (term89 A lt2) = (term90 A lt2).
Proof. exact (MK_COMB (@lem368635) (@lem368634 A lt2)). Qed.
Lemma lem368637 {A : Type'} (lt2 : type1402 A) (x : A) : (term86 A lt2 x) = (term79 A lt2 x).
Proof. exact (eq_refl (term86 A lt2 x)). Qed.
Lemma lem368638 {A : Type'} (lt2 : type1402 A) : (term91 A lt2) = (term85 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368637 A lt2 x)). Qed.
Lemma lem368639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368640 {A : Type'} (lt2 : type1402 A) : (term92 A lt2) = (term93 A lt2).
Proof. exact (MK_COMB (@lem368639 A) (@lem368638 A lt2)). Qed.
Lemma lem368641 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term57 A lt2).
Proof. exact (eq_refl (term57 A lt2)). Qed.
Lemma lem368642 {A : Type'} (lt2 : type1402 A) : (term84 A lt2) = (term94 A lt2).
Proof. exact (MK_COMB (@lem368641 A lt2) (@lem368640 A lt2)). Qed.
Lemma lem368643 {A : Type'} (lt2 : type1402 A) : ((term83 A lt2) = (term84 A lt2)) = ((term82 A lt2) = (term94 A lt2)).
Proof. exact (MK_COMB (@lem368636 A lt2) (@lem368642 A lt2)). Qed.
Lemma lem368644 {A : Type'} (lt2 : type1402 A) : (term82 A lt2) = (term94 A lt2).
Proof. exact (EQ_MP (@lem368643 A lt2) (@lem368628 A lt2)). Qed.
Lemma lem368697 {A : Type'} (lt2 : type1402 A) : (term63 A lt2) = (term94 A lt2).
Proof. exact (TRANS (@lem368624 A lt2) (@lem368644 A lt2)). Qed.
Lemma lem368698 {A : Type'} : (term64 A) = (term95 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368697 A lt2)). Qed.
Lemma lem368699 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368750 {A : Type'} : (term65 A) = (term96 A).
Proof. exact (MK_COMB (@lem368699 A) (@lem368698 A)). Qed.
Lemma lem368751 {A : Type'} : (term4 A) = (term96 A).
Proof. exact (TRANS (@lem368545 A) (@lem368750 A)). Qed.
Lemma lem368752 {A : Type'} (h1 : term4 A) : term96 A.
Proof. exact (EQ_MP (@lem368751 A) (@lem368457 A h1)). Qed.
Lemma lem368753 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term28 A lt2 x.
Proof. exact (h1). Qed.
Lemma lem368754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368762 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem368761 A (A -> Prop) f x). Qed.
Lemma lem368763 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem368762 A lt2 y). Qed.
Lemma lem368764 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem368765 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (lt2 y x) = (@I (A -> A -> Prop) lt2 y x).
Proof. exact (MK_COMB (@lem368763 A lt2 y) (@lem368764 A x)). Qed.
Lemma lem368767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368768 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem368767 A Prop f x). Qed.
Lemma lem368769 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) lt2 y x) = (term97 A lt2 y x).
Proof. exact (@lem368768 A (@I (A -> A -> Prop) lt2 y) x). Qed.
Lemma lem368771 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (lt2 y x) = (term97 A lt2 y x).
Proof. exact (TRANS (@lem368765 A lt2 y x) (@lem368769 A lt2 y x)). Qed.
Lemma lem368772 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term98 A lt2 y x) = (term99 A lt2 y x).
Proof. exact (MK_COMB (@lem368754) (@lem368771 A lt2 y x)). Qed.
Lemma lem368773 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368780 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368781 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem368780 A (A -> Prop) f x). Qed.
Lemma lem368782 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x) = (@I (A -> A -> Prop) lt2 x).
Proof. exact (@lem368781 A lt2 x). Qed.
Lemma lem368783 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem368784 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (lt2 x y) = (@I (A -> A -> Prop) lt2 x y).
Proof. exact (MK_COMB (@lem368782 A lt2 x) (@lem368783 A y)). Qed.
Lemma lem368786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368787 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem368786 A Prop f x). Qed.
Lemma lem368788 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) lt2 x y) = (term97 A lt2 x y).
Proof. exact (@lem368787 A (@I (A -> A -> Prop) lt2 x) y). Qed.
Lemma lem368790 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (lt2 x y) = (term97 A lt2 x y).
Proof. exact (TRANS (@lem368784 A lt2 x y) (@lem368788 A lt2 x y)). Qed.
Lemma lem368791 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term98 A lt2 x y) = (term99 A lt2 x y).
Proof. exact (MK_COMB (@lem368773) (@lem368790 A lt2 x y)). Qed.
Lemma lem368792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem368793 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term100 A lt2 x y) = (term101 A lt2 x y).
Proof. exact (MK_COMB (@lem368792) (@lem368791 A lt2 x y)). Qed.
Lemma lem368794 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term56 A lt2 y x) = (term102 A lt2 y x).
Proof. exact (MK_COMB (@lem368793 A lt2 x y) (@lem368772 A lt2 y x)). Qed.
Lemma lem368795 {A : Type'} (lt2 : type1402 A) (x : A) : (term71 A lt2 x) = (term103 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368794 A lt2 y x)). Qed.
Lemma lem368796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368797 {A : Type'} (lt2 : type1402 A) (x : A) : (term79 A lt2 x) = (term104 A lt2 x).
Proof. exact (MK_COMB (@lem368796 A) (@lem368795 A lt2 x)). Qed.
Lemma lem368798 {A : Type'} (lt2 : type1402 A) : (term85 A lt2) = (term105 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368797 A lt2 x)). Qed.
Lemma lem368799 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368800 {A : Type'} (lt2 : type1402 A) : (term93 A lt2) = (term106 A lt2).
Proof. exact (MK_COMB (@lem368799 A) (@lem368798 A lt2)). Qed.
Lemma lem368801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem368806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368807 {A : Type'} (f : type421 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> Prop) f x).
Proof. exact (@lem368806 (type1402 A) Prop f x). Qed.
Lemma lem368809 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem368807 A (@WF A) lt2). Qed.
Lemma lem368810 {A : Type'} (lt2 : type1402 A) : (term70 A lt2) = (term107 A lt2).
Proof. exact (MK_COMB (@lem368801) (@lem368809 A lt2)). Qed.
Lemma lem368811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem368812 {A : Type'} (lt2 : type1402 A) : (term57 A lt2) = (term108 A lt2).
Proof. exact (MK_COMB (@lem368811) (@lem368810 A lt2)). Qed.
Lemma lem368813 {A : Type'} (lt2 : type1402 A) : (term94 A lt2) = (term109 A lt2).
Proof. exact (MK_COMB (@lem368812 A lt2) (@lem368800 A lt2)). Qed.
Lemma lem368814 {A : Type'} : (term95 A) = (term110 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368813 A lt2)). Qed.
Lemma lem368815 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368816 {A : Type'} : (term96 A) = (term111 A).
Proof. exact (MK_COMB (@lem368815 A) (@lem368814 A)). Qed.
Lemma lem368817 {A : Type'} (h1 : term4 A) : term111 A.
Proof. exact (EQ_MP (@lem368816 A) (@lem368752 A h1)). Qed.
Lemma lem368824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368825 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem368824 A (A -> Prop) f x). Qed.
Lemma lem368826 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x) = (@I (A -> A -> Prop) lt2 x).
Proof. exact (@lem368825 A lt2 x). Qed.
Lemma lem368827 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem368828 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x x) = (@I (A -> A -> Prop) lt2 x x).
Proof. exact (MK_COMB (@lem368826 A lt2 x) (@lem368827 A x)). Qed.
Lemma lem368830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368831 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem368830 A Prop f x). Qed.
Lemma lem368832 {A : Type'} (lt2 : type1402 A) (x : A) : (@I (A -> A -> Prop) lt2 x x) = (term112 A lt2 x).
Proof. exact (@lem368831 A (@I (A -> A -> Prop) lt2 x) x). Qed.
Lemma lem368834 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x x) = (term112 A lt2 x).
Proof. exact (TRANS (@lem368828 A lt2 x) (@lem368832 A lt2 x)). Qed.
Lemma lem368839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem368840 {A : Type'} (f : type421 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> Prop) f x).
Proof. exact (@lem368839 (type1402 A) Prop f x). Qed.
Lemma lem368842 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem368840 A (@WF A) lt2). Qed.
Lemma lem368843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem368844 {A : Type'} (lt2 : type1402 A) : (term26 A lt2) = (term113 A lt2).
Proof. exact (MK_COMB (@lem368843) (@lem368842 A lt2)). Qed.
Lemma lem368845 {A : Type'} (lt2 : type1402 A) (x : A) : (term28 A lt2 x) = (term114 A lt2 x).
Proof. exact (MK_COMB (@lem368844 A lt2) (@lem368834 A lt2 x)). Qed.
Lemma lem368846 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term114 A lt2 x.
Proof. exact (EQ_MP (@lem368845 A lt2 x) (@lem368753 A lt2 x h1)). Qed.
Lemma lem368850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem368851 {A : Type'} (P : Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (@lem368850 A P Q). Qed.
Lemma lem368852 {A : Type'} (lt2 : type1402 A) : (term115 A lt2) = (term116 A lt2).
Proof. exact (@lem368851 A (term107 A lt2) (term105 A lt2)). Qed.
Lemma lem368853 {A : Type'} (lt2 : type1402 A) (x : A) : (term117 A lt2 x) = (term104 A lt2 x).
Proof. exact (eq_refl (term117 A lt2 x)). Qed.
Lemma lem368854 {A : Type'} (lt2 : type1402 A) : (term118 A lt2) = (term105 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368853 A lt2 x)). Qed.
Lemma lem368855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368856 {A : Type'} (lt2 : type1402 A) : (term119 A lt2) = (term106 A lt2).
Proof. exact (MK_COMB (@lem368855 A) (@lem368854 A lt2)). Qed.
Lemma lem368857 {A : Type'} (lt2 : type1402 A) : (term108 A lt2) = (term108 A lt2).
Proof. exact (eq_refl (term108 A lt2)). Qed.
Lemma lem368858 {A : Type'} (lt2 : type1402 A) : (term115 A lt2) = (term109 A lt2).
Proof. exact (MK_COMB (@lem368857 A lt2) (@lem368856 A lt2)). Qed.
Lemma lem368859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368860 {A : Type'} (lt2 : type1402 A) : (term120 A lt2) = (term121 A lt2).
Proof. exact (MK_COMB (@lem368859) (@lem368858 A lt2)). Qed.
Lemma lem368861 {A : Type'} (lt2 : type1402 A) (x : A) : (term117 A lt2 x) = (term104 A lt2 x).
Proof. exact (eq_refl (term117 A lt2 x)). Qed.
Lemma lem368862 {A : Type'} (lt2 : type1402 A) : (term108 A lt2) = (term108 A lt2).
Proof. exact (eq_refl (term108 A lt2)). Qed.
Lemma lem368863 {A : Type'} (lt2 : type1402 A) (x : A) : (term122 A lt2 x) = (term123 A lt2 x).
Proof. exact (MK_COMB (@lem368862 A lt2) (@lem368861 A lt2 x)). Qed.
Lemma lem368864 {A : Type'} (lt2 : type1402 A) : (term124 A lt2) = (term125 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368863 A lt2 x)). Qed.
Lemma lem368865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368866 {A : Type'} (lt2 : type1402 A) : (term116 A lt2) = (term126 A lt2).
Proof. exact (MK_COMB (@lem368865 A) (@lem368864 A lt2)). Qed.
Lemma lem368867 {A : Type'} (lt2 : type1402 A) : ((term115 A lt2) = (term116 A lt2)) = ((term109 A lt2) = (term126 A lt2)).
Proof. exact (MK_COMB (@lem368860 A lt2) (@lem368866 A lt2)). Qed.
Lemma lem368868 {A : Type'} (lt2 : type1402 A) : (term109 A lt2) = (term126 A lt2).
Proof. exact (EQ_MP (@lem368867 A lt2) (@lem368852 A lt2)). Qed.
Lemma lem368870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem368871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term67 A P Q) = (term66 A P Q).
Proof. exact (@lem368870 A P Q). Qed.
Lemma lem368872 {A : Type'} (lt2 : type1402 A) (x : A) : (term127 A lt2 x) = (term128 A lt2 x).
Proof. exact (@lem368871 A (term107 A lt2) (term103 A lt2 x)). Qed.
Lemma lem368873 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term129 A lt2 x y) = (term102 A lt2 y x).
Proof. exact (eq_refl (term129 A lt2 x y)). Qed.
Lemma lem368874 {A : Type'} (lt2 : type1402 A) (x : A) : (term130 A lt2 x) = (term103 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368873 A lt2 y x)). Qed.
Lemma lem368875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368876 {A : Type'} (lt2 : type1402 A) (x : A) : (term131 A lt2 x) = (term104 A lt2 x).
Proof. exact (MK_COMB (@lem368875 A) (@lem368874 A lt2 x)). Qed.
Lemma lem368877 {A : Type'} (lt2 : type1402 A) : (term108 A lt2) = (term108 A lt2).
Proof. exact (eq_refl (term108 A lt2)). Qed.
Lemma lem368878 {A : Type'} (lt2 : type1402 A) (x : A) : (term127 A lt2 x) = (term123 A lt2 x).
Proof. exact (MK_COMB (@lem368877 A lt2) (@lem368876 A lt2 x)). Qed.
Lemma lem368879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem368880 {A : Type'} (lt2 : type1402 A) (x : A) : (term132 A lt2 x) = (term133 A lt2 x).
Proof. exact (MK_COMB (@lem368879) (@lem368878 A lt2 x)). Qed.
Lemma lem368881 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term129 A lt2 x y) = (term102 A lt2 y x).
Proof. exact (eq_refl (term129 A lt2 x y)). Qed.
Lemma lem368882 {A : Type'} (lt2 : type1402 A) : (term108 A lt2) = (term108 A lt2).
Proof. exact (eq_refl (term108 A lt2)). Qed.
Lemma lem368883 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term134 A lt2 x y) = (term135 A lt2 y x).
Proof. exact (MK_COMB (@lem368882 A lt2) (@lem368881 A lt2 y x)). Qed.
Lemma lem368884 {A : Type'} (lt2 : type1402 A) (x : A) : (term136 A lt2 x) = (term137 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368883 A lt2 y x)). Qed.
Lemma lem368885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368886 {A : Type'} (lt2 : type1402 A) (x : A) : (term128 A lt2 x) = (term138 A lt2 x).
Proof. exact (MK_COMB (@lem368885 A) (@lem368884 A lt2 x)). Qed.
Lemma lem368887 {A : Type'} (lt2 : type1402 A) (x : A) : ((term127 A lt2 x) = (term128 A lt2 x)) = ((term123 A lt2 x) = (term138 A lt2 x)).
Proof. exact (MK_COMB (@lem368880 A lt2 x) (@lem368886 A lt2 x)). Qed.
Lemma lem368888 {A : Type'} (lt2 : type1402 A) (x : A) : (term123 A lt2 x) = (term138 A lt2 x).
Proof. exact (EQ_MP (@lem368887 A lt2 x) (@lem368872 A lt2 x)). Qed.
Lemma lem368889 {A : Type'} (lt2 : type1402 A) : (term125 A lt2) = (term139 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368888 A lt2 x)). Qed.
Lemma lem368890 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368891 {A : Type'} (lt2 : type1402 A) : (term126 A lt2) = (term140 A lt2).
Proof. exact (MK_COMB (@lem368890 A) (@lem368889 A lt2)). Qed.
Lemma lem368892 {A : Type'} (lt2 : type1402 A) : (term109 A lt2) = (term140 A lt2).
Proof. exact (TRANS (@lem368868 A lt2) (@lem368891 A lt2)). Qed.
Lemma lem368893 {A : Type'} : (term110 A) = (term141 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368892 A lt2)). Qed.
Lemma lem368894 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368895 {A : Type'} : (term111 A) = (term142 A).
Proof. exact (MK_COMB (@lem368894 A) (@lem368893 A)). Qed.
Lemma lem368908 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term135 A lt2 y x) = (term135 A lt2 y x).
Proof. exact (eq_refl (term135 A lt2 y x)). Qed.
Lemma lem368909 {A : Type'} (lt2 : type1402 A) (x : A) : (term137 A lt2 x) = (term137 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem368908 A lt2 y x)). Qed.
Lemma lem368910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368911 {A : Type'} (lt2 : type1402 A) (x : A) : (term138 A lt2 x) = (term138 A lt2 x).
Proof. exact (MK_COMB (@lem368910 A) (@lem368909 A lt2 x)). Qed.
Lemma lem368912 {A : Type'} (lt2 : type1402 A) : (term139 A lt2) = (term139 A lt2).
Proof. exact (fun_ext (fun x : A => @lem368911 A lt2 x)). Qed.
Lemma lem368913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem368914 {A : Type'} (lt2 : type1402 A) : (term140 A lt2) = (term140 A lt2).
Proof. exact (MK_COMB (@lem368913 A) (@lem368912 A lt2)). Qed.
Lemma lem368915 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem368914 A lt2)). Qed.
Lemma lem368916 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem368917 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem368916 A) (@lem368915 A)). Qed.
Lemma lem368918 {A : Type'} : (term111 A) = (term142 A).
Proof. exact (TRANS (@lem368895 A) (@lem368917 A)). Qed.
Lemma lem368919 {A : Type'} (h1 : term4 A) : term142 A.
Proof. exact (EQ_MP (@lem368918 A) (@lem368817 A h1)). Qed.
Lemma lem368928 {A : Type'} (_7989 : type1402 A) (h1 : term4 A) : term143 A _7989.
Proof. exact (@lem368919 A h1 _7989). Qed.
Lemma lem368929 {A : Type'} (_7989 : type1402 A) : (term143 A _7989) = (term140 A _7989).
Proof. exact (eq_refl (term143 A _7989)). Qed.
Lemma lem368930 {A : Type'} (_7989 : type1402 A) (h1 : term4 A) : term140 A _7989.
Proof. exact (EQ_MP (@lem368929 A _7989) (@lem368928 A _7989 h1)). Qed.
Lemma lem368931 {A : Type'} (_7989 : type1402 A) (_7990 : A) (h1 : term4 A) : term144 A _7989 _7990.
Proof. exact (@lem368930 A _7989 h1 _7990). Qed.
Lemma lem368932 {A : Type'} (_7989 : type1402 A) (_7990 : A) : (term144 A _7989 _7990) = (term138 A _7989 _7990).
Proof. exact (eq_refl (term144 A _7989 _7990)). Qed.
Lemma lem368933 {A : Type'} (_7989 : type1402 A) (_7990 : A) (h1 : term4 A) : term138 A _7989 _7990.
Proof. exact (EQ_MP (@lem368932 A _7989 _7990) (@lem368931 A _7989 _7990 h1)). Qed.
Lemma lem368934 {A : Type'} (_7989 : type1402 A) (_7990 : A) (_7991 : A) (h1 : term4 A) : term145 A _7989 _7990 _7991.
Proof. exact (@lem368933 A _7989 _7990 h1 _7991). Qed.
Lemma lem368935 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term145 A _7989 _7990 _7991) = (term135 A _7989 _7991 _7990).
Proof. exact (eq_refl (term145 A _7989 _7990 _7991)). Qed.
Lemma lem368946 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) (h1 : term4 A) : term135 A _7989 _7991 _7990.
Proof. exact (EQ_MP (@lem368935 A _7989 _7991 _7990) (@lem368934 A _7989 _7990 _7991 h1)). Qed.
Lemma lem368952 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (proj1 (@lem368846 A lt2 x h1)). Qed.
Lemma lem368953 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term146 A lt2.
Proof. exact (fun h0 : term107 A lt2 => @lem368952 A lt2 x h1). Qed.
Lemma lem368955 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368956 {A : Type'} (lt2 : type1402 A) : (term146 A lt2) = (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2).
Proof. exact (@lem368955 (@I ((A -> A -> Prop) -> Prop) (@WF A) lt2)). Qed.
Lemma lem368957 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : @I ((A -> A -> Prop) -> Prop) (@WF A) lt2.
Proof. exact (EQ_MP (@lem368956 A lt2) (@lem368953 A lt2 x h1)). Qed.
Lemma lem368959 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term112 A lt2 x.
Proof. exact (proj2 (@lem368846 A lt2 x h1)). Qed.
Lemma lem368960 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term148 A lt2 x.
Proof. exact (fun h0 : term149 A lt2 x => @lem368959 A lt2 x h1). Qed.
Lemma lem368962 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368963 {A : Type'} (lt2 : type1402 A) (x : A) : (term148 A lt2 x) = (term112 A lt2 x).
Proof. exact (@lem368962 (term112 A lt2 x)). Qed.
Lemma lem368964 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term112 A lt2 x.
Proof. exact (EQ_MP (@lem368963 A lt2 x) (@lem368960 A lt2 x h1)). Qed.
Lemma lem368966 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term112 A lt2 x.
Proof. exact (proj2 (@lem368846 A lt2 x h1)). Qed.
Lemma lem368967 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term148 A lt2 x.
Proof. exact (fun h0 : term149 A lt2 x => @lem368966 A lt2 x h1). Qed.
Lemma lem368969 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368970 {A : Type'} (lt2 : type1402 A) (x : A) : (term148 A lt2 x) = (term112 A lt2 x).
Proof. exact (@lem368969 (term112 A lt2 x)). Qed.
Lemma lem368971 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term112 A lt2 x.
Proof. exact (EQ_MP (@lem368970 A lt2 x) (@lem368967 A lt2 x h1)). Qed.
Lemma lem368973 (a : Prop) (b : Prop) : (term150 a b) = (term151 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem368974 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term102 A _7989 _7991 _7990) = (term152 A _7989 _7991 _7990).
Proof. exact (@lem368973 (term97 A _7989 _7990 _7991) (term97 A _7989 _7991 _7990)). Qed.
Lemma lem368975 {A : Type'} (_7989 : type1402 A) : (term108 A _7989) = (term108 A _7989).
Proof. exact (eq_refl (term108 A _7989)). Qed.
Lemma lem368976 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term135 A _7989 _7991 _7990) = (term153 A _7989 _7991 _7990).
Proof. exact (MK_COMB (@lem368975 A _7989) (@lem368974 A _7989 _7991 _7990)). Qed.
Lemma lem368978 (a : Prop) (b : Prop) : (term150 a b) = (term151 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem368979 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term153 A _7989 _7991 _7990) = (term154 A _7989 _7991 _7990).
Proof. exact (@lem368978 (@I ((A -> A -> Prop) -> Prop) (@WF A) _7989) (term155 A _7989 _7991 _7990)). Qed.
Lemma lem368980 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term135 A _7989 _7991 _7990) = (term154 A _7989 _7991 _7990).
Proof. exact (TRANS (@lem368976 A _7989 _7991 _7990) (@lem368979 A _7989 _7991 _7990)). Qed.
Lemma lem368982 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem368983 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term154 A _7989 _7991 _7990) = (term156 A _7989 _7991 _7990).
Proof. exact (@lem368982 (term157 A _7989 _7991 _7990)). Qed.
Lemma lem368984 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) : (term135 A _7989 _7991 _7990) = (term156 A _7989 _7991 _7990).
Proof. exact (TRANS (@lem368980 A _7989 _7991 _7990) (@lem368983 A _7989 _7991 _7990)). Qed.
Lemma lem368986 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term158 A lt2 x.
Proof. exact (conj (@lem368964 A lt2 x h1) (@lem368971 A lt2 x h1)). Qed.
Lemma lem368987 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term28 A lt2 x) : term159 A lt2 x.
Proof. exact (conj (@lem368957 A lt2 x h1) (@lem368986 A lt2 x h1)). Qed.
Lemma lem368989 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) (h1 : term4 A) : term156 A _7989 _7991 _7990.
Proof. exact (EQ_MP (@lem368984 A _7989 _7991 _7990) (@lem368946 A _7989 _7991 _7990 h1)). Qed.
Lemma lem368990 {A : Type'} (_7989 : type1402 A) (_7991 : A) (_7990 : A) (h1 : term4 A) : term156 A _7989 _7991 _7990.
Proof. exact (@lem368989 A _7989 _7991 _7990 h1). Qed.
Lemma lem368991 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term4 A) : term160 A lt2 x.
Proof. exact (@lem368990 A lt2 x x h1). Qed.
Lemma lem368994 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term4 A) (h2 : term28 A lt2 x) : False.
Proof. exact (@lem368991 A lt2 x h1 (@lem368987 A lt2 x h2)). Qed.
Lemma lem368995 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term4 A) (h2 : term28 A lt2 x) : term161.
Proof. exact (fun h0 : ~ False => @lem368994 A lt2 x h1 h2). Qed.
Lemma lem368997 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368998 : term161 = False.
Proof. exact (@lem368997 False). Qed.
Lemma lem368999 {A : Type'} (lt2 : type1402 A) (x : A) (h1 : term4 A) (h2 : term28 A lt2 x) : False.
Proof. exact (EQ_MP (@lem368998) (@lem368995 A lt2 x h1 h2)). Qed.
Lemma lem369000 {A : Type'} (lt2 : type1402 A) (h1 : term4 A) (h2 : term3 A lt2) : False.
Proof. exact (ex_elim (@lem368523 A lt2 h2) (fun x : A => fun h0 : term37 A lt2 x => @lem368999 A lt2 x h1 h0)). Qed.
Lemma lem369001 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term9 A.
Proof. exact (fun h0 : term4 A => @lem369000 A lt2 h0 h1). Qed.
Lemma lem369002 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem369003 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term10 A.
Proof. exact (EQ_MP (@lem369002 A) (@lem369001 A lt2 h1)). Qed.
Lemma lem369004 {A : Type'} (lt2 : type1402 A) : term12 A lt2.
Proof. exact (fun h0 : term3 A lt2 => @lem369003 A lt2 h0). Qed.
Lemma lem369009 {A : Type'} : term16 A.
Proof. exact (fun lt2 : type1402 A => @lem369004 A lt2). Qed.
Lemma lem369010 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem368455 A) (@lem369009 A)). Qed.
Lemma lem369011 {A : Type'} (lt2 : type1402 A) : term162 A lt2.
Proof. exact (@lem369010 A lt2). Qed.
Lemma lem369012 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term5 A lt2).
Proof. exact (eq_refl (term162 A lt2)). Qed.
Lemma lem369013 {A : Type'} (lt2 : type1402 A) : term5 A lt2.
Proof. exact (EQ_MP (@lem369012 A lt2) (@lem369011 A lt2)). Qed.
Lemma lem369015 {A : Type'} (lt2 : type1402 A) : term5 A lt2.
Proof. exact (@lem368327 A lt2 (@lem369013 A lt2)). Qed.
Lemma lem369016 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : term9 A.
Proof. exact (@lem369015 A lt2 (@lem368310 A lt2 h1)). Qed.
Lemma lem369017 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : False.
Proof. exact (@lem369016 A lt2 h1 (@lem368311 A)). Qed.
Lemma lem369018 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : (term3 A lt2) = False.
Proof. exact (prop_ext (fun h2 : term3 A lt2 => @lem369017 A lt2 h1) (fun h2 : False => @lem368310 A lt2 h1)). Qed.
Lemma lem369019 {A : Type'} (lt2 : type1402 A) (h1 : term3 A lt2) : False.
Proof. exact (EQ_MP (@lem369018 A lt2 h1) (@lem368310 A lt2 h1)). Qed.
Lemma lem369020 {A : Type'} (lt2 : type1402 A) : term2 A lt2.
Proof. exact (fun h0 : term3 A lt2 => @lem369019 A lt2 h0). Qed.
Lemma lem369021 {A : Type'} (lt2 : type1402 A) : term1 A lt2.
Proof. exact (EQ_MP (@lem368309 A lt2) (@lem369020 A lt2)). Qed.
