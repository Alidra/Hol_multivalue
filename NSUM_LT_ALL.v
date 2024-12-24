Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LT_IMP_LE_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NSUM_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm69_spec.
Lemma lem6934234 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6934235 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6934236 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6934235 t1) (@lem6934234 t1)). Qed.
Lemma lem6934237 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6934236 t1 t2). Qed.
Lemma lem6934238 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6934239 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6934238 t1 t2) (@lem6934237 t1 t2)). Qed.
Lemma lem6934240 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6934239 t1 t2 t3). Qed.
Lemma lem6934241 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6934242 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6934241 t1 t2 t3) (@lem6934240 t1 t2 t3)). Qed.
Lemma lem6934243 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6934242 t1 t2 t3)). Qed.
Lemma lem6934245 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6934246 {_127128 : Type'} : (term8 _127128) = (term9 _127128).
Proof. exact (@lem6934245 (term8 _127128)). Qed.
Lemma lem6934247 {_127128 : Type'} : (term9 _127128) = (term8 _127128).
Proof. exact (SYM (@lem6934246 _127128)). Qed.
Lemma lem6934248 {_127128 : Type'} (h1 : term10 _127128) : term10 _127128.
Proof. exact (h1). Qed.
Lemma lem6934249 {_127128 : Type'} : term11 _127128.
Proof. exact (@lem3216368 _127128). Qed.
Lemma lem6934252 {_127128 : Type'} : term12 _127128.
Proof. exact (@lem6934233 _127128). Qed.
Lemma lem6934257 {_127128 A : Type'} (h1 : term13 _127128 A) : term13 _127128 A.
Proof. exact (h1). Qed.
Lemma lem6934258 {_127128 A : Type'} : term14 _127128 A.
Proof. exact (fun h0 : term13 _127128 A => @lem6934257 _127128 A h0). Qed.
Lemma lem6934259 {_127128 A : Type'} (h1 : term14 _127128 A) : term14 _127128 A.
Proof. exact (h1). Qed.
Lemma lem6934260 {_127128 A : Type'} (h1 : term13 _127128 A) : term13 _127128 A.
Proof. exact (h1). Qed.
Lemma lem6934261 {_127128 A : Type'} (h1 : term13 _127128 A) (h2 : term14 _127128 A) : term13 _127128 A.
Proof. exact (@lem6934259 _127128 A h2 (@lem6934260 _127128 A h1)). Qed.
Lemma lem6934262 {_127128 A : Type'} (h1 : term13 _127128 A) : term15 _127128 A.
Proof. exact (fun h0 : term14 _127128 A => @lem6934261 _127128 A h1 h0). Qed.
Lemma lem6934263 {_127128 A : Type'} (h1 : term14 _127128 A) : term14 _127128 A.
Proof. exact (h1). Qed.
Lemma lem6934264 {_127128 A : Type'} (h1 : term13 _127128 A) (h2 : term14 _127128 A) : term13 _127128 A.
Proof. exact (@lem6934262 _127128 A h1 (@lem6934263 _127128 A h2)). Qed.
Lemma lem6934265 {_127128 A : Type'} (h1 : term14 _127128 A) : term14 _127128 A.
Proof. exact (fun h0 : term13 _127128 A => @lem6934264 _127128 A h0 h1). Qed.
Lemma lem6934266 {_127128 A : Type'} : term16 _127128 A.
Proof. exact (fun h0 : term14 _127128 A => @lem6934265 _127128 A h0). Qed.
Lemma lem6934269 {_127128 A : Type'} : term14 _127128 A.
Proof. exact (@lem6934266 _127128 A (@lem6934258 _127128 A)). Qed.
Lemma lem6934270 {_127128 A : Type'} : term14 _127128 A.
Proof. exact (@lem6934269 _127128 A). Qed.
Lemma lem6934462 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6934463 {_127128 : Type'} : (term17 _127128) = (term18 _127128).
Proof. exact (@lem6934462 (term11 _127128)). Qed.
Lemma lem6934472 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem6934473 {_127128 : Type'} : (term20 _127128) = (term21 _127128).
Proof. exact (MK_COMB (@lem6934472) (@lem6934463 _127128)). Qed.
Lemma lem6934476 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem6934477 {_127128 A : Type'} : (term23 _127128 A) = (term24 _127128 A).
Proof. exact (MK_COMB (@lem6934476 A) (@lem6934473 _127128)). Qed.
Lemma lem6934480 {_127128 : Type'} : (term22 _127128) = (term22 _127128).
Proof. exact (eq_refl (term22 _127128)). Qed.
Lemma lem6934481 {_127128 A : Type'} : (term25 _127128 A) = (term26 _127128 A).
Proof. exact (MK_COMB (@lem6934480 _127128) (@lem6934477 _127128 A)). Qed.
Lemma lem6934484 {_127128 : Type'} : (term27 _127128) = (term27 _127128).
Proof. exact (eq_refl (term27 _127128)). Qed.
Lemma lem6934491 {_127128 A : Type'} : (term13 _127128 A) = (term28 _127128 A).
Proof. exact (MK_COMB (@lem6934484 _127128) (@lem6934481 _127128 A)). Qed.
Lemma lem6934494 {_127128 : Type'} (s : _127128 -> Prop) : (term29 _127128 s) = (term29 _127128 s).
Proof. exact (eq_refl (term29 _127128 s)). Qed.
Lemma lem6934495 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (@IN _127128 x s).
Proof. exact (eq_refl (@IN _127128 x s)). Qed.
Lemma lem6934496 {_127128 : Type'} (s : _127128 -> Prop) : (term30 _127128 s) = (term30 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6934495 _127128 x s)). Qed.
Lemma lem6934497 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6934498 {_127128 : Type'} (s : _127128 -> Prop) : (term31 _127128 s) = (term31 _127128 s).
Proof. exact (MK_COMB (@lem6934497 _127128) (@lem6934496 _127128 s)). Qed.
Lemma lem6934499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6934500 {_127128 : Type'} (s : _127128 -> Prop) : (term32 _127128 s) = (term32 _127128 s).
Proof. exact (MK_COMB (@lem6934499) (@lem6934498 _127128 s)). Qed.
Lemma lem6934501 {_127128 : Type'} (s : _127128 -> Prop) : ((term31 _127128 s) = (term29 _127128 s)) = ((term31 _127128 s) = (term29 _127128 s)).
Proof. exact (MK_COMB (@lem6934500 _127128 s) (@lem6934494 _127128 s)). Qed.
Lemma lem6934502 {_127128 : Type'} : (term33 _127128) = (term33 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6934501 _127128 s)). Qed.
Lemma lem6934503 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6934504 {_127128 : Type'} : (term11 _127128) = (term11 _127128).
Proof. exact (MK_COMB (@lem6934503 _127128) (@lem6934502 _127128)). Qed.
Lemma lem6934505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934506 {_127128 : Type'} : (term18 _127128) = (term18 _127128).
Proof. exact (MK_COMB (@lem6934505) (@lem6934504 _127128)). Qed.
Lemma lem6934511 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem6934512 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem6934511 m n)). Qed.
Lemma lem6934513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6934514 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem6934513) (@lem6934512 m)). Qed.
Lemma lem6934515 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem6934514 m)). Qed.
Lemma lem6934516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6934517 : term38 = term38.
Proof. exact (MK_COMB (@lem6934516) (@lem6934515)). Qed.
Lemma lem6934518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934519 : term19 = term19.
Proof. exact (MK_COMB (@lem6934518) (@lem6934517)). Qed.
Lemma lem6934520 {_127128 : Type'} : (term21 _127128) = (term21 _127128).
Proof. exact (MK_COMB (@lem6934519) (@lem6934506 _127128)). Qed.
Lemma lem6934521 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem6934526 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term40 A s f g x) = (term40 A s f g x).
Proof. exact (eq_refl (term40 A s f g x)). Qed.
Lemma lem6934527 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term41 A s f g) = (term41 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6934526 A s f g x)). Qed.
Lemma lem6934528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6934529 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term42 A s f g) = (term42 A s f g).
Proof. exact (MK_COMB (@lem6934528 A) (@lem6934527 A s f g)). Qed.
Lemma lem6934534 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term43 A s f g x) = (term43 A s f g x).
Proof. exact (eq_refl (term43 A s f g x)). Qed.
Lemma lem6934535 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term44 A s f g) = (term44 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6934534 A s f g x)). Qed.
Lemma lem6934536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6934537 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term45 A s f g) = (term45 A s f g).
Proof. exact (MK_COMB (@lem6934536 A) (@lem6934535 A s f g)). Qed.
Lemma lem6934538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6934539 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term46 A s f g) = (term46 A s f g).
Proof. exact (MK_COMB (@lem6934538) (@lem6934537 A s f g)). Qed.
Lemma lem6934540 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term47 A s f g) = (term47 A s f g).
Proof. exact (MK_COMB (@lem6934539 A s f g) (@lem6934529 A s f g)). Qed.
Lemma lem6934543 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem6934544 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term49 A s f g) = (term49 A s f g).
Proof. exact (MK_COMB (@lem6934543 A s) (@lem6934540 A s f g)). Qed.
Lemma lem6934545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934546 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term50 A s f g) = (term50 A s f g).
Proof. exact (MK_COMB (@lem6934545) (@lem6934544 A s f g)). Qed.
Lemma lem6934547 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term51 A f s g) = (term51 A f s g).
Proof. exact (MK_COMB (@lem6934546 A s f g) (@lem6934521 A f s g)). Qed.
Lemma lem6934548 {A : Type'} (f : A -> nat) (g : A -> nat) : (term52 A f g) = (term52 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6934547 A f s g)). Qed.
Lemma lem6934549 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6934550 {A : Type'} (f : A -> nat) (g : A -> nat) : (term53 A f g) = (term53 A f g).
Proof. exact (MK_COMB (@lem6934549 A) (@lem6934548 A f g)). Qed.
Lemma lem6934551 {A : Type'} (f : A -> nat) : (term54 A f) = (term54 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6934550 A f g)). Qed.
Lemma lem6934552 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6934553 {A : Type'} (f : A -> nat) : (term55 A f) = (term55 A f).
Proof. exact (MK_COMB (@lem6934552 A) (@lem6934551 A f)). Qed.
Lemma lem6934554 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6934553 A f)). Qed.
Lemma lem6934555 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6934556 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem6934555 A) (@lem6934554 A)). Qed.
Lemma lem6934557 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934558 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem6934557) (@lem6934556 A)). Qed.
Lemma lem6934559 {_127128 A : Type'} : (term24 _127128 A) = (term24 _127128 A).
Proof. exact (MK_COMB (@lem6934558 A) (@lem6934520 _127128)). Qed.
Lemma lem6934560 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6934565 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term40 _127128 s f g x) = (term40 _127128 s f g x).
Proof. exact (eq_refl (term40 _127128 s f g x)). Qed.
Lemma lem6934566 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term41 _127128 s f g) = (term41 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934565 _127128 s f g x)). Qed.
Lemma lem6934567 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6934568 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term42 _127128 s f g) = (term42 _127128 s f g).
Proof. exact (MK_COMB (@lem6934567 _127128) (@lem6934566 _127128 s f g)). Qed.
Lemma lem6934573 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term43 _127128 s f g x) = (term43 _127128 s f g x).
Proof. exact (eq_refl (term43 _127128 s f g x)). Qed.
Lemma lem6934574 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term44 _127128 s f g) = (term44 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934573 _127128 s f g x)). Qed.
Lemma lem6934575 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6934576 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term45 _127128 s f g) = (term45 _127128 s f g).
Proof. exact (MK_COMB (@lem6934575 _127128) (@lem6934574 _127128 s f g)). Qed.
Lemma lem6934577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6934578 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term46 _127128 s f g) = (term46 _127128 s f g).
Proof. exact (MK_COMB (@lem6934577) (@lem6934576 _127128 s f g)). Qed.
Lemma lem6934579 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term47 _127128 s f g) = (term47 _127128 s f g).
Proof. exact (MK_COMB (@lem6934578 _127128 s f g) (@lem6934568 _127128 s f g)). Qed.
Lemma lem6934582 {_127128 : Type'} (s : _127128 -> Prop) : (term48 _127128 s) = (term48 _127128 s).
Proof. exact (eq_refl (term48 _127128 s)). Qed.
Lemma lem6934583 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term49 _127128 s f g) = (term49 _127128 s f g).
Proof. exact (MK_COMB (@lem6934582 _127128 s) (@lem6934579 _127128 s f g)). Qed.
Lemma lem6934584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934585 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term50 _127128 s f g) = (term50 _127128 s f g).
Proof. exact (MK_COMB (@lem6934584) (@lem6934583 _127128 s f g)). Qed.
Lemma lem6934586 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term51 _127128 f s g) = (term51 _127128 f s g).
Proof. exact (MK_COMB (@lem6934585 _127128 s f g) (@lem6934560 _127128 f s g)). Qed.
Lemma lem6934587 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term52 _127128 f g) = (term52 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6934586 _127128 f s g)). Qed.
Lemma lem6934588 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6934589 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term53 _127128 f g) = (term53 _127128 f g).
Proof. exact (MK_COMB (@lem6934588 _127128) (@lem6934587 _127128 f g)). Qed.
Lemma lem6934590 {_127128 : Type'} (f : _127128 -> nat) : (term54 _127128 f) = (term54 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6934589 _127128 f g)). Qed.
Lemma lem6934591 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6934592 {_127128 : Type'} (f : _127128 -> nat) : (term55 _127128 f) = (term55 _127128 f).
Proof. exact (MK_COMB (@lem6934591 _127128) (@lem6934590 _127128 f)). Qed.
Lemma lem6934593 {_127128 : Type'} : (term56 _127128) = (term56 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6934592 _127128 f)). Qed.
Lemma lem6934594 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6934595 {_127128 : Type'} : (term12 _127128) = (term12 _127128).
Proof. exact (MK_COMB (@lem6934594 _127128) (@lem6934593 _127128)). Qed.
Lemma lem6934596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934597 {_127128 : Type'} : (term22 _127128) = (term22 _127128).
Proof. exact (MK_COMB (@lem6934596) (@lem6934595 _127128)). Qed.
Lemma lem6934598 {_127128 A : Type'} : (term26 _127128 A) = (term26 _127128 A).
Proof. exact (MK_COMB (@lem6934597 _127128) (@lem6934559 _127128 A)). Qed.
Lemma lem6934599 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6934604 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term57 _127128 s f g x) = (term57 _127128 s f g x).
Proof. exact (eq_refl (term57 _127128 s f g x)). Qed.
Lemma lem6934605 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term58 _127128 s f g) = (term58 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934604 _127128 s f g x)). Qed.
Lemma lem6934606 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6934607 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term59 _127128 s f g) = (term59 _127128 s f g).
Proof. exact (MK_COMB (@lem6934606 _127128) (@lem6934605 _127128 s f g)). Qed.
Lemma lem6934612 {_127128 : Type'} (s : _127128 -> Prop) : (term60 _127128 s) = (term60 _127128 s).
Proof. exact (eq_refl (term60 _127128 s)). Qed.
Lemma lem6934613 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term61 _127128 s f g) = (term61 _127128 s f g).
Proof. exact (MK_COMB (@lem6934612 _127128 s) (@lem6934607 _127128 s f g)). Qed.
Lemma lem6934616 {_127128 : Type'} (s : _127128 -> Prop) : (term48 _127128 s) = (term48 _127128 s).
Proof. exact (eq_refl (term48 _127128 s)). Qed.
Lemma lem6934617 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term62 _127128 s f g) = (term62 _127128 s f g).
Proof. exact (MK_COMB (@lem6934616 _127128 s) (@lem6934613 _127128 s f g)). Qed.
Lemma lem6934618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934619 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term63 _127128 s f g) = (term63 _127128 s f g).
Proof. exact (MK_COMB (@lem6934618) (@lem6934617 _127128 s f g)). Qed.
Lemma lem6934620 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term64 _127128 f s g) = (term64 _127128 f s g).
Proof. exact (MK_COMB (@lem6934619 _127128 s f g) (@lem6934599 _127128 f s g)). Qed.
Lemma lem6934621 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term65 _127128 f g) = (term65 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6934620 _127128 f s g)). Qed.
Lemma lem6934622 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6934623 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term66 _127128 f g) = (term66 _127128 f g).
Proof. exact (MK_COMB (@lem6934622 _127128) (@lem6934621 _127128 f g)). Qed.
Lemma lem6934624 {_127128 : Type'} (f : _127128 -> nat) : (term67 _127128 f) = (term67 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6934623 _127128 f g)). Qed.
Lemma lem6934625 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6934626 {_127128 : Type'} (f : _127128 -> nat) : (term68 _127128 f) = (term68 _127128 f).
Proof. exact (MK_COMB (@lem6934625 _127128) (@lem6934624 _127128 f)). Qed.
Lemma lem6934627 {_127128 : Type'} : (term69 _127128) = (term69 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6934626 _127128 f)). Qed.
Lemma lem6934628 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6934629 {_127128 : Type'} : (term8 _127128) = (term8 _127128).
Proof. exact (MK_COMB (@lem6934628 _127128) (@lem6934627 _127128)). Qed.
Lemma lem6934630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934631 {_127128 : Type'} : (term10 _127128) = (term10 _127128).
Proof. exact (MK_COMB (@lem6934630) (@lem6934629 _127128)). Qed.
Lemma lem6934632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6934633 {_127128 : Type'} : (term27 _127128) = (term27 _127128).
Proof. exact (MK_COMB (@lem6934632) (@lem6934631 _127128)). Qed.
Lemma lem6934634 {_127128 A : Type'} : (term28 _127128 A) = (term28 _127128 A).
Proof. exact (MK_COMB (@lem6934633 _127128) (@lem6934598 _127128 A)). Qed.
Lemma lem6934783 {_127128 A : Type'} : (term13 _127128 A) = (term28 _127128 A).
Proof. exact (TRANS (@lem6934491 _127128 A) (@lem6934634 _127128 A)). Qed.
Lemma lem6934784 {_127128 A : Type'} : (term28 _127128 A) = (term13 _127128 A).
Proof. exact (SYM (@lem6934783 _127128 A)). Qed.
Lemma lem6934785 {_127128 : Type'} (h1 : term10 _127128) : term10 _127128.
Proof. exact (h1). Qed.
Lemma lem6934786 {_127128 : Type'} (h1 : term12 _127128) : term12 _127128.
Proof. exact (h1). Qed.
Lemma lem6934787 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6934788 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem6934789 {_127128 : Type'} (h1 : term11 _127128) : term11 _127128.
Proof. exact (h1). Qed.
Lemma lem6934798 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term57 _127128 s f g x) = (term70 _127128 s f g x).
Proof. exact (@lem17265 (@IN _127128 x s) (term71 _127128 f g x)). Qed.
Lemma lem6934799 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term58 _127128 s f g) = (term72 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934798 _127128 s f g x)). Qed.
Lemma lem6934800 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6934801 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term59 _127128 s f g) = (term73 _127128 s f g).
Proof. exact (MK_COMB (@lem6934800 _127128) (@lem6934799 _127128 s f g)). Qed.
Lemma lem6934803 {_127128 : Type'} (s : _127128 -> Prop) : (term60 _127128 s) = (term60 _127128 s).
Proof. exact (eq_refl (term60 _127128 s)). Qed.
Lemma lem6934804 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term61 _127128 s f g) = (term74 _127128 s f g).
Proof. exact (MK_COMB (@lem6934803 _127128 s) (@lem6934801 _127128 s f g)). Qed.
Lemma lem6934806 {_127128 : Type'} (s : _127128 -> Prop) : (term48 _127128 s) = (term48 _127128 s).
Proof. exact (eq_refl (term48 _127128 s)). Qed.
Lemma lem6934807 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term62 _127128 s f g) = (term75 _127128 s f g).
Proof. exact (MK_COMB (@lem6934806 _127128 s) (@lem6934804 _127128 s f g)). Qed.
Lemma lem6934808 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term76 _127128 f s g) = (term76 _127128 f s g).
Proof. exact (eq_refl (term76 _127128 f s g)). Qed.
Lemma lem6934809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6934810 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term77 _127128 s f g) = (term78 _127128 s f g).
Proof. exact (MK_COMB (@lem6934809) (@lem6934807 _127128 s f g)). Qed.
Lemma lem6934811 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term79 _127128 f s g) = (term80 _127128 f s g).
Proof. exact (MK_COMB (@lem6934810 _127128 s f g) (@lem6934808 _127128 f s g)). Qed.
Lemma lem6934812 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term81 _127128 f s g) = (term79 _127128 f s g).
Proof. exact (@lem17362 (term62 _127128 s f g) (term39 _127128 f s g)). Qed.
Lemma lem6934813 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term81 _127128 f s g) = (term80 _127128 f s g).
Proof. exact (TRANS (@lem6934812 _127128 f s g) (@lem6934811 _127128 f s g)). Qed.
Lemma lem6934814 {_127128 : Type'} (P : type686 _127128) : (term82 _127128 P) = (term83 _127128 P).
Proof. exact (@lem18392 (_127128 -> Prop) P). Qed.
Lemma lem6934815 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term84 _127128 f g) = (term85 _127128 f g).
Proof. exact (@lem6934814 _127128 (term65 _127128 f g)). Qed.
Lemma lem6934816 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term86 _127128 f g s) = (term64 _127128 f s g).
Proof. exact (eq_refl (term86 _127128 f g s)). Qed.
Lemma lem6934817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934818 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term87 _127128 f g s) = (term81 _127128 f s g).
Proof. exact (MK_COMB (@lem6934817) (@lem6934816 _127128 f s g)). Qed.
Lemma lem6934819 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term87 _127128 f g s) = (term80 _127128 f s g).
Proof. exact (TRANS (@lem6934818 _127128 f s g) (@lem6934813 _127128 f s g)). Qed.
Lemma lem6934820 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term88 _127128 f g) = (term89 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6934819 _127128 f s g)). Qed.
Lemma lem6934821 {_127128 : Type'} : (@ex (_127128 -> Prop)) = (@ex (_127128 -> Prop)).
Proof. exact (eq_refl (@ex (_127128 -> Prop))). Qed.
Lemma lem6934822 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term85 _127128 f g) = (term90 _127128 f g).
Proof. exact (MK_COMB (@lem6934821 _127128) (@lem6934820 _127128 f g)). Qed.
Lemma lem6934823 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term84 _127128 f g) = (term90 _127128 f g).
Proof. exact (TRANS (@lem6934815 _127128 f g) (@lem6934822 _127128 f g)). Qed.
Lemma lem6934824 {_127128 : Type'} (P : type704 _127128) : (term91 _127128 P) = (term92 _127128 P).
Proof. exact (@lem18392 (_127128 -> nat) P). Qed.
Lemma lem6934825 {_127128 : Type'} (f : _127128 -> nat) : (term93 _127128 f) = (term94 _127128 f).
Proof. exact (@lem6934824 _127128 (term67 _127128 f)). Qed.
Lemma lem6934826 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term95 _127128 f g) = (term66 _127128 f g).
Proof. exact (eq_refl (term95 _127128 f g)). Qed.
Lemma lem6934827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934828 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term96 _127128 f g) = (term84 _127128 f g).
Proof. exact (MK_COMB (@lem6934827) (@lem6934826 _127128 f g)). Qed.
Lemma lem6934829 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term96 _127128 f g) = (term90 _127128 f g).
Proof. exact (TRANS (@lem6934828 _127128 f g) (@lem6934823 _127128 f g)). Qed.
Lemma lem6934830 {_127128 : Type'} (f : _127128 -> nat) : (term97 _127128 f) = (term98 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6934829 _127128 f g)). Qed.
Lemma lem6934831 {_127128 : Type'} : (@ex (_127128 -> nat)) = (@ex (_127128 -> nat)).
Proof. exact (eq_refl (@ex (_127128 -> nat))). Qed.
Lemma lem6934832 {_127128 : Type'} (f : _127128 -> nat) : (term94 _127128 f) = (term99 _127128 f).
Proof. exact (MK_COMB (@lem6934831 _127128) (@lem6934830 _127128 f)). Qed.
Lemma lem6934833 {_127128 : Type'} (f : _127128 -> nat) : (term93 _127128 f) = (term99 _127128 f).
Proof. exact (TRANS (@lem6934825 _127128 f) (@lem6934832 _127128 f)). Qed.
Lemma lem6934834 {_127128 : Type'} (P : type704 _127128) : (term91 _127128 P) = (term92 _127128 P).
Proof. exact (@lem18392 (_127128 -> nat) P). Qed.
Lemma lem6934835 {_127128 : Type'} : (term10 _127128) = (term100 _127128).
Proof. exact (@lem6934834 _127128 (term69 _127128)). Qed.
Lemma lem6934836 {_127128 : Type'} (f : _127128 -> nat) : (term101 _127128 f) = (term68 _127128 f).
Proof. exact (eq_refl (term101 _127128 f)). Qed.
Lemma lem6934837 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934838 {_127128 : Type'} (f : _127128 -> nat) : (term102 _127128 f) = (term93 _127128 f).
Proof. exact (MK_COMB (@lem6934837) (@lem6934836 _127128 f)). Qed.
Lemma lem6934839 {_127128 : Type'} (f : _127128 -> nat) : (term102 _127128 f) = (term99 _127128 f).
Proof. exact (TRANS (@lem6934838 _127128 f) (@lem6934833 _127128 f)). Qed.
Lemma lem6934840 {_127128 : Type'} : (term103 _127128) = (term104 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6934839 _127128 f)). Qed.
Lemma lem6934841 {_127128 : Type'} : (@ex (_127128 -> nat)) = (@ex (_127128 -> nat)).
Proof. exact (eq_refl (@ex (_127128 -> nat))). Qed.
Lemma lem6934842 {_127128 : Type'} : (term100 _127128) = (term105 _127128).
Proof. exact (MK_COMB (@lem6934841 _127128) (@lem6934840 _127128)). Qed.
Lemma lem6934951 {_127128 : Type'} : (term10 _127128) = (term105 _127128).
Proof. exact (TRANS (@lem6934835 _127128) (@lem6934842 _127128)). Qed.
Lemma lem6934952 {_127128 : Type'} (h1 : term10 _127128) : term105 _127128.
Proof. exact (EQ_MP (@lem6934951 _127128) (@lem6934785 _127128 h1)). Qed.
Lemma lem6934960 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term106 _127128 s f g x) = (term107 _127128 s f g x).
Proof. exact (@lem17362 (@IN _127128 x s) (term108 _127128 f g x)). Qed.
Lemma lem6934961 {_127128 : Type'} (P : _127128 -> Prop) : (term109 _127128 P) = (term110 _127128 P).
Proof. exact (@lem18392 _127128 P). Qed.
Lemma lem6934962 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term111 _127128 s f g) = (term112 _127128 s f g).
Proof. exact (@lem6934961 _127128 (term44 _127128 s f g)). Qed.
Lemma lem6934963 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term113 _127128 s f g x) = (term43 _127128 s f g x).
Proof. exact (eq_refl (term113 _127128 s f g x)). Qed.
Lemma lem6934964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934965 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term114 _127128 s f g x) = (term106 _127128 s f g x).
Proof. exact (MK_COMB (@lem6934964) (@lem6934963 _127128 s f g x)). Qed.
Lemma lem6934966 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term114 _127128 s f g x) = (term107 _127128 s f g x).
Proof. exact (TRANS (@lem6934965 _127128 s f g x) (@lem6934960 _127128 s f g x)). Qed.
Lemma lem6934967 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term115 _127128 s f g) = (term116 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934966 _127128 s f g x)). Qed.
Lemma lem6934968 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6934969 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term112 _127128 s f g) = (term117 _127128 s f g).
Proof. exact (MK_COMB (@lem6934968 _127128) (@lem6934967 _127128 s f g)). Qed.
Lemma lem6934970 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term111 _127128 s f g) = (term117 _127128 s f g).
Proof. exact (TRANS (@lem6934962 _127128 s f g) (@lem6934969 _127128 s f g)). Qed.
Lemma lem6934977 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term118 _127128 s f g x) = (term119 _127128 s f g x).
Proof. exact (@lem17045 (@IN _127128 x s) (term71 _127128 f g x)). Qed.
Lemma lem6934978 {_127128 : Type'} (P : _127128 -> Prop) : (term120 _127128 P) = (term121 _127128 P).
Proof. exact (@lem18394 _127128 P). Qed.
Lemma lem6934979 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term122 _127128 s f g) = (term123 _127128 s f g).
Proof. exact (@lem6934978 _127128 (term41 _127128 s f g)). Qed.
Lemma lem6934980 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term124 _127128 s f g x) = (term40 _127128 s f g x).
Proof. exact (eq_refl (term124 _127128 s f g x)). Qed.
Lemma lem6934981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6934982 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term125 _127128 s f g x) = (term118 _127128 s f g x).
Proof. exact (MK_COMB (@lem6934981) (@lem6934980 _127128 s f g x)). Qed.
Lemma lem6934983 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term125 _127128 s f g x) = (term119 _127128 s f g x).
Proof. exact (TRANS (@lem6934982 _127128 s f g x) (@lem6934977 _127128 s f g x)). Qed.
Lemma lem6934984 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term126 _127128 s f g) = (term127 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6934983 _127128 s f g x)). Qed.
Lemma lem6934985 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6934986 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term123 _127128 s f g) = (term128 _127128 s f g).
Proof. exact (MK_COMB (@lem6934985 _127128) (@lem6934984 _127128 s f g)). Qed.
Lemma lem6934987 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term122 _127128 s f g) = (term128 _127128 s f g).
Proof. exact (TRANS (@lem6934979 _127128 s f g) (@lem6934986 _127128 s f g)). Qed.
Lemma lem6934988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6934989 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term129 _127128 s f g) = (term130 _127128 s f g).
Proof. exact (MK_COMB (@lem6934988) (@lem6934970 _127128 s f g)). Qed.
Lemma lem6934990 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term131 _127128 s f g) = (term132 _127128 s f g).
Proof. exact (MK_COMB (@lem6934989 _127128 s f g) (@lem6934987 _127128 s f g)). Qed.
Lemma lem6934991 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term133 _127128 s f g) = (term131 _127128 s f g).
Proof. exact (@lem17045 (term45 _127128 s f g) (term42 _127128 s f g)). Qed.
Lemma lem6934992 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term133 _127128 s f g) = (term132 _127128 s f g).
Proof. exact (TRANS (@lem6934991 _127128 s f g) (@lem6934990 _127128 s f g)). Qed.
Lemma lem6934994 {_127128 : Type'} (s : _127128 -> Prop) : (term134 _127128 s) = (term134 _127128 s).
Proof. exact (eq_refl (term134 _127128 s)). Qed.
Lemma lem6934995 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term135 _127128 s f g) = (term136 _127128 s f g).
Proof. exact (MK_COMB (@lem6934994 _127128 s) (@lem6934992 _127128 s f g)). Qed.
Lemma lem6934996 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term137 _127128 s f g) = (term135 _127128 s f g).
Proof. exact (@lem17045 (@FINITE _127128 s) (term47 _127128 s f g)). Qed.
Lemma lem6934997 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term137 _127128 s f g) = (term136 _127128 s f g).
Proof. exact (TRANS (@lem6934996 _127128 s f g) (@lem6934995 _127128 s f g)). Qed.
Lemma lem6934998 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6934999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935000 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term138 _127128 s f g) = (term139 _127128 s f g).
Proof. exact (MK_COMB (@lem6934999) (@lem6934997 _127128 s f g)). Qed.
Lemma lem6935001 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term140 _127128 f s g) = (term141 _127128 f s g).
Proof. exact (MK_COMB (@lem6935000 _127128 s f g) (@lem6934998 _127128 f s g)). Qed.
Lemma lem6935002 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term51 _127128 f s g) = (term140 _127128 f s g).
Proof. exact (@lem17265 (term49 _127128 s f g) (term39 _127128 f s g)). Qed.
Lemma lem6935003 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term51 _127128 f s g) = (term141 _127128 f s g).
Proof. exact (TRANS (@lem6935002 _127128 f s g) (@lem6935001 _127128 f s g)). Qed.
Lemma lem6935004 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term52 _127128 f g) = (term142 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935003 _127128 f s g)). Qed.
Lemma lem6935005 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935006 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term53 _127128 f g) = (term143 _127128 f g).
Proof. exact (MK_COMB (@lem6935005 _127128) (@lem6935004 _127128 f g)). Qed.
Lemma lem6935007 {_127128 : Type'} (f : _127128 -> nat) : (term54 _127128 f) = (term144 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6935006 _127128 f g)). Qed.
Lemma lem6935008 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935009 {_127128 : Type'} (f : _127128 -> nat) : (term55 _127128 f) = (term145 _127128 f).
Proof. exact (MK_COMB (@lem6935008 _127128) (@lem6935007 _127128 f)). Qed.
Lemma lem6935010 {_127128 : Type'} : (term56 _127128) = (term146 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6935009 _127128 f)). Qed.
Lemma lem6935011 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935012 {_127128 : Type'} : (term12 _127128) = (term147 _127128).
Proof. exact (MK_COMB (@lem6935011 _127128) (@lem6935010 _127128)). Qed.
Lemma lem6935167 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6935168 {_127128 : Type'} (P : _127128 -> Prop) (Q : Prop) : (term148 _127128 P Q) = (term149 _127128 P Q).
Proof. exact (@lem6935167 _127128 P Q). Qed.
Lemma lem6935169 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term150 _127128 s f g) = (term151 _127128 s f g).
Proof. exact (@lem6935168 _127128 (term116 _127128 s f g) (term128 _127128 s f g)). Qed.
Lemma lem6935170 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term152 _127128 s f g x) = (term107 _127128 s f g x).
Proof. exact (eq_refl (term152 _127128 s f g x)). Qed.
Lemma lem6935171 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term153 _127128 s f g) = (term116 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935170 _127128 s f g x)). Qed.
Lemma lem6935172 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935173 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term154 _127128 s f g) = (term117 _127128 s f g).
Proof. exact (MK_COMB (@lem6935172 _127128) (@lem6935171 _127128 s f g)). Qed.
Lemma lem6935174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935175 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term155 _127128 s f g) = (term130 _127128 s f g).
Proof. exact (MK_COMB (@lem6935174) (@lem6935173 _127128 s f g)). Qed.
Lemma lem6935176 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term128 _127128 s f g) = (term128 _127128 s f g).
Proof. exact (eq_refl (term128 _127128 s f g)). Qed.
Lemma lem6935177 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term150 _127128 s f g) = (term132 _127128 s f g).
Proof. exact (MK_COMB (@lem6935175 _127128 s f g) (@lem6935176 _127128 s f g)). Qed.
Lemma lem6935178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935179 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term156 _127128 s f g) = (term157 _127128 s f g).
Proof. exact (MK_COMB (@lem6935178) (@lem6935177 _127128 s f g)). Qed.
Lemma lem6935180 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term152 _127128 s f g x) = (term107 _127128 s f g x).
Proof. exact (eq_refl (term152 _127128 s f g x)). Qed.
Lemma lem6935181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935182 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term158 _127128 s f g x) = (term159 _127128 s f g x).
Proof. exact (MK_COMB (@lem6935181) (@lem6935180 _127128 s f g x)). Qed.
Lemma lem6935183 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term128 _127128 s f g) = (term128 _127128 s f g).
Proof. exact (eq_refl (term128 _127128 s f g)). Qed.
Lemma lem6935184 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term160 _127128 x s f g) = (term161 _127128 x s f g).
Proof. exact (MK_COMB (@lem6935182 _127128 s f g x) (@lem6935183 _127128 s f g)). Qed.
Lemma lem6935185 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term162 _127128 s f g) = (term163 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935184 _127128 x s f g)). Qed.
Lemma lem6935186 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935187 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term151 _127128 s f g) = (term164 _127128 s f g).
Proof. exact (MK_COMB (@lem6935186 _127128) (@lem6935185 _127128 s f g)). Qed.
Lemma lem6935188 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : ((term150 _127128 s f g) = (term151 _127128 s f g)) = ((term132 _127128 s f g) = (term164 _127128 s f g)).
Proof. exact (MK_COMB (@lem6935179 _127128 s f g) (@lem6935187 _127128 s f g)). Qed.
Lemma lem6935189 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term132 _127128 s f g) = (term164 _127128 s f g).
Proof. exact (EQ_MP (@lem6935188 _127128 s f g) (@lem6935169 _127128 s f g)). Qed.
Lemma lem6935190 {_127128 : Type'} (s : _127128 -> Prop) : (term134 _127128 s) = (term134 _127128 s).
Proof. exact (eq_refl (term134 _127128 s)). Qed.
Lemma lem6935191 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term136 _127128 s f g) = (term165 _127128 s f g).
Proof. exact (MK_COMB (@lem6935190 _127128 s) (@lem6935189 _127128 s f g)). Qed.
Lemma lem6935193 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6935194 {_127128 : Type'} (P : Prop) (Q : _127128 -> Prop) : (term166 _127128 P Q) = (term167 _127128 P Q).
Proof. exact (@lem6935193 _127128 P Q). Qed.
Lemma lem6935195 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term168 _127128 s f g) = (term169 _127128 s f g).
Proof. exact (@lem6935194 _127128 (term170 _127128 s) (term163 _127128 s f g)). Qed.
Lemma lem6935196 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term171 _127128 s f g x) = (term161 _127128 x s f g).
Proof. exact (eq_refl (term171 _127128 s f g x)). Qed.
Lemma lem6935197 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term172 _127128 s f g) = (term163 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935196 _127128 x s f g)). Qed.
Lemma lem6935198 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935199 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term173 _127128 s f g) = (term164 _127128 s f g).
Proof. exact (MK_COMB (@lem6935198 _127128) (@lem6935197 _127128 s f g)). Qed.
Lemma lem6935200 {_127128 : Type'} (s : _127128 -> Prop) : (term134 _127128 s) = (term134 _127128 s).
Proof. exact (eq_refl (term134 _127128 s)). Qed.
Lemma lem6935201 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term168 _127128 s f g) = (term165 _127128 s f g).
Proof. exact (MK_COMB (@lem6935200 _127128 s) (@lem6935199 _127128 s f g)). Qed.
Lemma lem6935202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935203 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term174 _127128 s f g) = (term175 _127128 s f g).
Proof. exact (MK_COMB (@lem6935202) (@lem6935201 _127128 s f g)). Qed.
Lemma lem6935204 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term171 _127128 s f g x) = (term161 _127128 x s f g).
Proof. exact (eq_refl (term171 _127128 s f g x)). Qed.
Lemma lem6935205 {_127128 : Type'} (s : _127128 -> Prop) : (term134 _127128 s) = (term134 _127128 s).
Proof. exact (eq_refl (term134 _127128 s)). Qed.
Lemma lem6935206 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term176 _127128 s f g x) = (term177 _127128 x s f g).
Proof. exact (MK_COMB (@lem6935205 _127128 s) (@lem6935204 _127128 x s f g)). Qed.
Lemma lem6935207 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term178 _127128 s f g) = (term179 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935206 _127128 x s f g)). Qed.
Lemma lem6935208 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935209 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term169 _127128 s f g) = (term180 _127128 s f g).
Proof. exact (MK_COMB (@lem6935208 _127128) (@lem6935207 _127128 s f g)). Qed.
Lemma lem6935210 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : ((term168 _127128 s f g) = (term169 _127128 s f g)) = ((term165 _127128 s f g) = (term180 _127128 s f g)).
Proof. exact (MK_COMB (@lem6935203 _127128 s f g) (@lem6935209 _127128 s f g)). Qed.
Lemma lem6935211 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term165 _127128 s f g) = (term180 _127128 s f g).
Proof. exact (EQ_MP (@lem6935210 _127128 s f g) (@lem6935195 _127128 s f g)). Qed.
Lemma lem6935212 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term136 _127128 s f g) = (term180 _127128 s f g).
Proof. exact (TRANS (@lem6935191 _127128 s f g) (@lem6935211 _127128 s f g)). Qed.
Lemma lem6935213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935214 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term139 _127128 s f g) = (term181 _127128 s f g).
Proof. exact (MK_COMB (@lem6935213) (@lem6935212 _127128 s f g)). Qed.
Lemma lem6935215 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6935216 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term141 _127128 f s g) = (term182 _127128 f s g).
Proof. exact (MK_COMB (@lem6935214 _127128 s f g) (@lem6935215 _127128 f s g)). Qed.
Lemma lem6935218 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6935219 {_127128 : Type'} (P : _127128 -> Prop) (Q : Prop) : (term148 _127128 P Q) = (term149 _127128 P Q).
Proof. exact (@lem6935218 _127128 P Q). Qed.
Lemma lem6935220 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term183 _127128 f s g) = (term184 _127128 f s g).
Proof. exact (@lem6935219 _127128 (term179 _127128 s f g) (term39 _127128 f s g)). Qed.
Lemma lem6935221 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term185 _127128 s f g x) = (term177 _127128 x s f g).
Proof. exact (eq_refl (term185 _127128 s f g x)). Qed.
Lemma lem6935222 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term186 _127128 s f g) = (term179 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935221 _127128 x s f g)). Qed.
Lemma lem6935223 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935224 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term187 _127128 s f g) = (term180 _127128 s f g).
Proof. exact (MK_COMB (@lem6935223 _127128) (@lem6935222 _127128 s f g)). Qed.
Lemma lem6935225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935226 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term188 _127128 s f g) = (term181 _127128 s f g).
Proof. exact (MK_COMB (@lem6935225) (@lem6935224 _127128 s f g)). Qed.
Lemma lem6935227 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6935228 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term183 _127128 f s g) = (term182 _127128 f s g).
Proof. exact (MK_COMB (@lem6935226 _127128 s f g) (@lem6935227 _127128 f s g)). Qed.
Lemma lem6935229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935230 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term189 _127128 f s g) = (term190 _127128 f s g).
Proof. exact (MK_COMB (@lem6935229) (@lem6935228 _127128 f s g)). Qed.
Lemma lem6935231 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term185 _127128 s f g x) = (term177 _127128 x s f g).
Proof. exact (eq_refl (term185 _127128 s f g x)). Qed.
Lemma lem6935232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935233 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term191 _127128 s f g x) = (term192 _127128 x s f g).
Proof. exact (MK_COMB (@lem6935232) (@lem6935231 _127128 x s f g)). Qed.
Lemma lem6935234 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term39 _127128 f s g).
Proof. exact (eq_refl (term39 _127128 f s g)). Qed.
Lemma lem6935235 {_127128 : Type'} (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term193 _127128 x f s g) = (term194 _127128 x f s g).
Proof. exact (MK_COMB (@lem6935233 _127128 x s f g) (@lem6935234 _127128 f s g)). Qed.
Lemma lem6935236 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term195 _127128 f s g) = (term196 _127128 f s g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935235 _127128 x f s g)). Qed.
Lemma lem6935237 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935238 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term184 _127128 f s g) = (term197 _127128 f s g).
Proof. exact (MK_COMB (@lem6935237 _127128) (@lem6935236 _127128 f s g)). Qed.
Lemma lem6935239 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : ((term183 _127128 f s g) = (term184 _127128 f s g)) = ((term182 _127128 f s g) = (term197 _127128 f s g)).
Proof. exact (MK_COMB (@lem6935230 _127128 f s g) (@lem6935238 _127128 f s g)). Qed.
Lemma lem6935240 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term182 _127128 f s g) = (term197 _127128 f s g).
Proof. exact (EQ_MP (@lem6935239 _127128 f s g) (@lem6935220 _127128 f s g)). Qed.
Lemma lem6935241 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term141 _127128 f s g) = (term197 _127128 f s g).
Proof. exact (TRANS (@lem6935216 _127128 f s g) (@lem6935240 _127128 f s g)). Qed.
Lemma lem6935242 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term142 _127128 f g) = (term198 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935241 _127128 f s g)). Qed.
Lemma lem6935243 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935244 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term143 _127128 f g) = (term199 _127128 f g).
Proof. exact (MK_COMB (@lem6935243 _127128) (@lem6935242 _127128 f g)). Qed.
Lemma lem6935246 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935247 {_127128 : Type'} (P : type672 _127128) : (term202 _127128 P) = (term203 _127128 P).
Proof. exact (@lem6935246 (_127128 -> Prop) _127128 P). Qed.
Lemma lem6935248 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term204 _127128 f g) = (term205 _127128 f g).
Proof. exact (@lem6935247 _127128 (term206 _127128 f g)). Qed.
Lemma lem6935249 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term207 _127128 f g s) = (term196 _127128 f s g).
Proof. exact (eq_refl (term207 _127128 f g s)). Qed.
Lemma lem6935250 {_127128 : Type'} (x : _127128) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935251 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (x : _127128) : (term208 _127128 f g s x) = (term209 _127128 f s g x).
Proof. exact (MK_COMB (@lem6935249 _127128 f s g) (@lem6935250 _127128 x)). Qed.
Lemma lem6935252 {_127128 : Type'} (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term209 _127128 f s g x) = (term194 _127128 x f s g).
Proof. exact (eq_refl (term209 _127128 f s g x)). Qed.
Lemma lem6935253 {_127128 : Type'} (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term208 _127128 f g s x) = (term194 _127128 x f s g).
Proof. exact (TRANS (@lem6935251 _127128 f s g x) (@lem6935252 _127128 x f s g)). Qed.
Lemma lem6935254 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term210 _127128 f g s) = (term196 _127128 f s g).
Proof. exact (fun_ext (fun x : _127128 => @lem6935253 _127128 x f s g)). Qed.
Lemma lem6935255 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935256 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term211 _127128 f g s) = (term197 _127128 f s g).
Proof. exact (MK_COMB (@lem6935255 _127128) (@lem6935254 _127128 f s g)). Qed.
Lemma lem6935257 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term212 _127128 f g) = (term198 _127128 f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935256 _127128 f s g)). Qed.
Lemma lem6935258 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935259 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term204 _127128 f g) = (term199 _127128 f g).
Proof. exact (MK_COMB (@lem6935258 _127128) (@lem6935257 _127128 f g)). Qed.
Lemma lem6935260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935261 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term213 _127128 f g) = (term214 _127128 f g).
Proof. exact (MK_COMB (@lem6935260) (@lem6935259 _127128 f g)). Qed.
Lemma lem6935262 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term207 _127128 f g s) = (term196 _127128 f s g).
Proof. exact (eq_refl (term207 _127128 f g s)). Qed.
Lemma lem6935263 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6935264 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) (s : _127128 -> Prop) : (term215 _127128 f g x s) = (term216 _127128 f g x s).
Proof. exact (MK_COMB (@lem6935262 _127128 f s g) (@lem6935263 _127128 x s)). Qed.
Lemma lem6935265 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term216 _127128 f g x s) = (term217 _127128 x f s g).
Proof. exact (eq_refl (term216 _127128 f g x s)). Qed.
Lemma lem6935266 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term215 _127128 f g x s) = (term217 _127128 x f s g).
Proof. exact (TRANS (@lem6935264 _127128 f g x s) (@lem6935265 _127128 x f s g)). Qed.
Lemma lem6935267 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term218 _127128 f g x) = (term219 _127128 x f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935266 _127128 x f s g)). Qed.
Lemma lem6935268 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935269 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term220 _127128 f g x) = (term221 _127128 x f g).
Proof. exact (MK_COMB (@lem6935268 _127128) (@lem6935267 _127128 x f g)). Qed.
Lemma lem6935270 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term222 _127128 f g) = (term223 _127128 f g).
Proof. exact (fun_ext (fun x : type684 _127128 => @lem6935269 _127128 x f g)). Qed.
Lemma lem6935271 {_127128 : Type'} : (@ex ((_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> Prop) -> _127128))). Qed.
Lemma lem6935272 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term205 _127128 f g) = (term224 _127128 f g).
Proof. exact (MK_COMB (@lem6935271 _127128) (@lem6935270 _127128 f g)). Qed.
Lemma lem6935273 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : ((term204 _127128 f g) = (term205 _127128 f g)) = ((term199 _127128 f g) = (term224 _127128 f g)).
Proof. exact (MK_COMB (@lem6935261 _127128 f g) (@lem6935272 _127128 f g)). Qed.
Lemma lem6935274 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term199 _127128 f g) = (term224 _127128 f g).
Proof. exact (EQ_MP (@lem6935273 _127128 f g) (@lem6935248 _127128 f g)). Qed.
Lemma lem6935275 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term143 _127128 f g) = (term224 _127128 f g).
Proof. exact (TRANS (@lem6935244 _127128 f g) (@lem6935274 _127128 f g)). Qed.
Lemma lem6935276 {_127128 : Type'} (f : _127128 -> nat) : (term144 _127128 f) = (term225 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6935275 _127128 f g)). Qed.
Lemma lem6935277 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935278 {_127128 : Type'} (f : _127128 -> nat) : (term145 _127128 f) = (term226 _127128 f).
Proof. exact (MK_COMB (@lem6935277 _127128) (@lem6935276 _127128 f)). Qed.
Lemma lem6935280 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935281 {_127128 : Type'} (P : type690 _127128) : (term227 _127128 P) = (term228 _127128 P).
Proof. exact (@lem6935280 (_127128 -> nat) (type684 _127128) P). Qed.
Lemma lem6935282 {_127128 : Type'} (f : _127128 -> nat) : (term229 _127128 f) = (term230 _127128 f).
Proof. exact (@lem6935281 _127128 (term231 _127128 f)). Qed.
Lemma lem6935283 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term232 _127128 f g) = (term223 _127128 f g).
Proof. exact (eq_refl (term232 _127128 f g)). Qed.
Lemma lem6935284 {_127128 : Type'} (x : type684 _127128) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935285 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) : (term233 _127128 f g x) = (term234 _127128 f g x).
Proof. exact (MK_COMB (@lem6935283 _127128 f g) (@lem6935284 _127128 x)). Qed.
Lemma lem6935286 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term234 _127128 f g x) = (term221 _127128 x f g).
Proof. exact (eq_refl (term234 _127128 f g x)). Qed.
Lemma lem6935287 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term233 _127128 f g x) = (term221 _127128 x f g).
Proof. exact (TRANS (@lem6935285 _127128 f g x) (@lem6935286 _127128 x f g)). Qed.
Lemma lem6935288 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term235 _127128 f g) = (term223 _127128 f g).
Proof. exact (fun_ext (fun x : type684 _127128 => @lem6935287 _127128 x f g)). Qed.
Lemma lem6935289 {_127128 : Type'} : (@ex ((_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> Prop) -> _127128))). Qed.
Lemma lem6935290 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term236 _127128 f g) = (term224 _127128 f g).
Proof. exact (MK_COMB (@lem6935289 _127128) (@lem6935288 _127128 f g)). Qed.
Lemma lem6935291 {_127128 : Type'} (f : _127128 -> nat) : (term237 _127128 f) = (term225 _127128 f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6935290 _127128 f g)). Qed.
Lemma lem6935292 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935293 {_127128 : Type'} (f : _127128 -> nat) : (term229 _127128 f) = (term226 _127128 f).
Proof. exact (MK_COMB (@lem6935292 _127128) (@lem6935291 _127128 f)). Qed.
Lemma lem6935294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935295 {_127128 : Type'} (f : _127128 -> nat) : (term238 _127128 f) = (term239 _127128 f).
Proof. exact (MK_COMB (@lem6935294) (@lem6935293 _127128 f)). Qed.
Lemma lem6935296 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) : (term232 _127128 f g) = (term223 _127128 f g).
Proof. exact (eq_refl (term232 _127128 f g)). Qed.
Lemma lem6935297 {_127128 : Type'} (x : type694 _127128) (g : _127128 -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem6935298 {_127128 : Type'} (f : _127128 -> nat) (x : type694 _127128) (g : _127128 -> nat) : (term240 _127128 f x g) = (term241 _127128 f x g).
Proof. exact (MK_COMB (@lem6935296 _127128 f g) (@lem6935297 _127128 x g)). Qed.
Lemma lem6935299 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term241 _127128 f x g) = (term242 _127128 x f g).
Proof. exact (eq_refl (term241 _127128 f x g)). Qed.
Lemma lem6935300 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term240 _127128 f x g) = (term242 _127128 x f g).
Proof. exact (TRANS (@lem6935298 _127128 f x g) (@lem6935299 _127128 x f g)). Qed.
Lemma lem6935301 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) : (term243 _127128 f x) = (term244 _127128 x f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6935300 _127128 x f g)). Qed.
Lemma lem6935302 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935303 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) : (term245 _127128 f x) = (term246 _127128 x f).
Proof. exact (MK_COMB (@lem6935302 _127128) (@lem6935301 _127128 x f)). Qed.
Lemma lem6935304 {_127128 : Type'} (f : _127128 -> nat) : (term247 _127128 f) = (term248 _127128 f).
Proof. exact (fun_ext (fun x : type694 _127128 => @lem6935303 _127128 x f)). Qed.
Lemma lem6935305 {_127128 : Type'} : (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128))). Qed.
Lemma lem6935306 {_127128 : Type'} (f : _127128 -> nat) : (term230 _127128 f) = (term249 _127128 f).
Proof. exact (MK_COMB (@lem6935305 _127128) (@lem6935304 _127128 f)). Qed.
Lemma lem6935307 {_127128 : Type'} (f : _127128 -> nat) : ((term229 _127128 f) = (term230 _127128 f)) = ((term226 _127128 f) = (term249 _127128 f)).
Proof. exact (MK_COMB (@lem6935295 _127128 f) (@lem6935306 _127128 f)). Qed.
Lemma lem6935308 {_127128 : Type'} (f : _127128 -> nat) : (term226 _127128 f) = (term249 _127128 f).
Proof. exact (EQ_MP (@lem6935307 _127128 f) (@lem6935282 _127128 f)). Qed.
Lemma lem6935309 {_127128 : Type'} (f : _127128 -> nat) : (term145 _127128 f) = (term249 _127128 f).
Proof. exact (TRANS (@lem6935278 _127128 f) (@lem6935308 _127128 f)). Qed.
Lemma lem6935310 {_127128 : Type'} : (term146 _127128) = (term250 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6935309 _127128 f)). Qed.
Lemma lem6935311 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935312 {_127128 : Type'} : (term147 _127128) = (term251 _127128).
Proof. exact (MK_COMB (@lem6935311 _127128) (@lem6935310 _127128)). Qed.
Lemma lem6935314 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935315 {_127128 : Type'} (P : type691 _127128) : (term252 _127128 P) = (term253 _127128 P).
Proof. exact (@lem6935314 (_127128 -> nat) (type694 _127128) P). Qed.
Lemma lem6935316 {_127128 : Type'} : (term254 _127128) = (term255 _127128).
Proof. exact (@lem6935315 _127128 (term256 _127128)). Qed.
Lemma lem6935317 {_127128 : Type'} (f : _127128 -> nat) : (term257 _127128 f) = (term248 _127128 f).
Proof. exact (eq_refl (term257 _127128 f)). Qed.
Lemma lem6935318 {_127128 : Type'} (x : type694 _127128) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935319 {_127128 : Type'} (f : _127128 -> nat) (x : type694 _127128) : (term258 _127128 f x) = (term259 _127128 f x).
Proof. exact (MK_COMB (@lem6935317 _127128 f) (@lem6935318 _127128 x)). Qed.
Lemma lem6935320 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) : (term259 _127128 f x) = (term246 _127128 x f).
Proof. exact (eq_refl (term259 _127128 f x)). Qed.
Lemma lem6935321 {_127128 : Type'} (x : type694 _127128) (f : _127128 -> nat) : (term258 _127128 f x) = (term246 _127128 x f).
Proof. exact (TRANS (@lem6935319 _127128 f x) (@lem6935320 _127128 x f)). Qed.
Lemma lem6935322 {_127128 : Type'} (f : _127128 -> nat) : (term260 _127128 f) = (term248 _127128 f).
Proof. exact (fun_ext (fun x : type694 _127128 => @lem6935321 _127128 x f)). Qed.
Lemma lem6935323 {_127128 : Type'} : (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> nat) -> (_127128 -> Prop) -> _127128))). Qed.
Lemma lem6935324 {_127128 : Type'} (f : _127128 -> nat) : (term261 _127128 f) = (term249 _127128 f).
Proof. exact (MK_COMB (@lem6935323 _127128) (@lem6935322 _127128 f)). Qed.
Lemma lem6935325 {_127128 : Type'} : (term262 _127128) = (term250 _127128).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6935324 _127128 f)). Qed.
Lemma lem6935326 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935327 {_127128 : Type'} : (term254 _127128) = (term251 _127128).
Proof. exact (MK_COMB (@lem6935326 _127128) (@lem6935325 _127128)). Qed.
Lemma lem6935328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935329 {_127128 : Type'} : (term263 _127128) = (term264 _127128).
Proof. exact (MK_COMB (@lem6935328) (@lem6935327 _127128)). Qed.
Lemma lem6935330 {_127128 : Type'} (f : _127128 -> nat) : (term257 _127128 f) = (term248 _127128 f).
Proof. exact (eq_refl (term257 _127128 f)). Qed.
Lemma lem6935331 {_127128 : Type'} (x : type695 _127128) (f : _127128 -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6935332 {_127128 : Type'} (x : type695 _127128) (f : _127128 -> nat) : (term265 _127128 x f) = (term266 _127128 x f).
Proof. exact (MK_COMB (@lem6935330 _127128 f) (@lem6935331 _127128 x f)). Qed.
Lemma lem6935333 {_127128 : Type'} (x : type695 _127128) (f : _127128 -> nat) : (term266 _127128 x f) = (term267 _127128 x f).
Proof. exact (eq_refl (term266 _127128 x f)). Qed.
Lemma lem6935334 {_127128 : Type'} (x : type695 _127128) (f : _127128 -> nat) : (term265 _127128 x f) = (term267 _127128 x f).
Proof. exact (TRANS (@lem6935332 _127128 x f) (@lem6935333 _127128 x f)). Qed.
Lemma lem6935335 {_127128 : Type'} (x : type695 _127128) : (term268 _127128 x) = (term269 _127128 x).
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6935334 _127128 x f)). Qed.
Lemma lem6935336 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6935337 {_127128 : Type'} (x : type695 _127128) : (term270 _127128 x) = (term271 _127128 x).
Proof. exact (MK_COMB (@lem6935336 _127128) (@lem6935335 _127128 x)). Qed.
Lemma lem6935338 {_127128 : Type'} : (term272 _127128) = (term273 _127128).
Proof. exact (fun_ext (fun x : type695 _127128 => @lem6935337 _127128 x)). Qed.
Lemma lem6935339 {_127128 : Type'} : (@ex ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128))). Qed.
Lemma lem6935340 {_127128 : Type'} : (term255 _127128) = (term274 _127128).
Proof. exact (MK_COMB (@lem6935339 _127128) (@lem6935338 _127128)). Qed.
Lemma lem6935341 {_127128 : Type'} : ((term254 _127128) = (term255 _127128)) = ((term251 _127128) = (term274 _127128)).
Proof. exact (MK_COMB (@lem6935329 _127128) (@lem6935340 _127128)). Qed.
Lemma lem6935342 {_127128 : Type'} : (term251 _127128) = (term274 _127128).
Proof. exact (EQ_MP (@lem6935341 _127128) (@lem6935316 _127128)). Qed.
Lemma lem6935344 {_127128 : Type'} : (term147 _127128) = (term274 _127128).
Proof. exact (TRANS (@lem6935312 _127128) (@lem6935342 _127128)). Qed.
Lemma lem6935345 {_127128 : Type'} : (term12 _127128) = (term274 _127128).
Proof. exact (TRANS (@lem6935012 _127128) (@lem6935344 _127128)). Qed.
Lemma lem6935346 {_127128 : Type'} (h1 : term12 _127128) : term274 _127128.
Proof. exact (EQ_MP (@lem6935345 _127128) (@lem6934786 _127128 h1)). Qed.
Lemma lem6935354 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term106 A s f g x) = (term107 A s f g x).
Proof. exact (@lem17362 (@IN A x s) (term108 A f g x)). Qed.
Lemma lem6935355 {A : Type'} (P : A -> Prop) : (term109 A P) = (term110 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6935356 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term111 A s f g) = (term112 A s f g).
Proof. exact (@lem6935355 A (term44 A s f g)). Qed.
Lemma lem6935357 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term113 A s f g x) = (term43 A s f g x).
Proof. exact (eq_refl (term113 A s f g x)). Qed.
Lemma lem6935358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6935359 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term114 A s f g x) = (term106 A s f g x).
Proof. exact (MK_COMB (@lem6935358) (@lem6935357 A s f g x)). Qed.
Lemma lem6935360 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term114 A s f g x) = (term107 A s f g x).
Proof. exact (TRANS (@lem6935359 A s f g x) (@lem6935354 A s f g x)). Qed.
Lemma lem6935361 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term115 A s f g) = (term116 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935360 A s f g x)). Qed.
Lemma lem6935362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935363 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term112 A s f g) = (term117 A s f g).
Proof. exact (MK_COMB (@lem6935362 A) (@lem6935361 A s f g)). Qed.
Lemma lem6935364 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term111 A s f g) = (term117 A s f g).
Proof. exact (TRANS (@lem6935356 A s f g) (@lem6935363 A s f g)). Qed.
Lemma lem6935371 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term118 A s f g x) = (term119 A s f g x).
Proof. exact (@lem17045 (@IN A x s) (term71 A f g x)). Qed.
Lemma lem6935372 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6935373 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term122 A s f g) = (term123 A s f g).
Proof. exact (@lem6935372 A (term41 A s f g)). Qed.
Lemma lem6935374 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term124 A s f g x) = (term40 A s f g x).
Proof. exact (eq_refl (term124 A s f g x)). Qed.
Lemma lem6935375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6935376 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term125 A s f g x) = (term118 A s f g x).
Proof. exact (MK_COMB (@lem6935375) (@lem6935374 A s f g x)). Qed.
Lemma lem6935377 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term125 A s f g x) = (term119 A s f g x).
Proof. exact (TRANS (@lem6935376 A s f g x) (@lem6935371 A s f g x)). Qed.
Lemma lem6935378 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term126 A s f g) = (term127 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935377 A s f g x)). Qed.
Lemma lem6935379 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6935380 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term123 A s f g) = (term128 A s f g).
Proof. exact (MK_COMB (@lem6935379 A) (@lem6935378 A s f g)). Qed.
Lemma lem6935381 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term122 A s f g) = (term128 A s f g).
Proof. exact (TRANS (@lem6935373 A s f g) (@lem6935380 A s f g)). Qed.
Lemma lem6935382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935383 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term129 A s f g) = (term130 A s f g).
Proof. exact (MK_COMB (@lem6935382) (@lem6935364 A s f g)). Qed.
Lemma lem6935384 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term131 A s f g) = (term132 A s f g).
Proof. exact (MK_COMB (@lem6935383 A s f g) (@lem6935381 A s f g)). Qed.
Lemma lem6935385 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term133 A s f g) = (term131 A s f g).
Proof. exact (@lem17045 (term45 A s f g) (term42 A s f g)). Qed.
Lemma lem6935386 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term133 A s f g) = (term132 A s f g).
Proof. exact (TRANS (@lem6935385 A s f g) (@lem6935384 A s f g)). Qed.
Lemma lem6935388 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem6935389 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term135 A s f g) = (term136 A s f g).
Proof. exact (MK_COMB (@lem6935388 A s) (@lem6935386 A s f g)). Qed.
Lemma lem6935390 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term137 A s f g) = (term135 A s f g).
Proof. exact (@lem17045 (@FINITE A s) (term47 A s f g)). Qed.
Lemma lem6935391 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term137 A s f g) = (term136 A s f g).
Proof. exact (TRANS (@lem6935390 A s f g) (@lem6935389 A s f g)). Qed.
Lemma lem6935392 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem6935393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935394 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term138 A s f g) = (term139 A s f g).
Proof. exact (MK_COMB (@lem6935393) (@lem6935391 A s f g)). Qed.
Lemma lem6935395 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term140 A f s g) = (term141 A f s g).
Proof. exact (MK_COMB (@lem6935394 A s f g) (@lem6935392 A f s g)). Qed.
Lemma lem6935396 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term51 A f s g) = (term140 A f s g).
Proof. exact (@lem17265 (term49 A s f g) (term39 A f s g)). Qed.
Lemma lem6935397 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term51 A f s g) = (term141 A f s g).
Proof. exact (TRANS (@lem6935396 A f s g) (@lem6935395 A f s g)). Qed.
Lemma lem6935398 {A : Type'} (f : A -> nat) (g : A -> nat) : (term52 A f g) = (term142 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6935397 A f s g)). Qed.
Lemma lem6935399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6935400 {A : Type'} (f : A -> nat) (g : A -> nat) : (term53 A f g) = (term143 A f g).
Proof. exact (MK_COMB (@lem6935399 A) (@lem6935398 A f g)). Qed.
Lemma lem6935401 {A : Type'} (f : A -> nat) : (term54 A f) = (term144 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6935400 A f g)). Qed.
Lemma lem6935402 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935403 {A : Type'} (f : A -> nat) : (term55 A f) = (term145 A f).
Proof. exact (MK_COMB (@lem6935402 A) (@lem6935401 A f)). Qed.
Lemma lem6935404 {A : Type'} : (term56 A) = (term146 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6935403 A f)). Qed.
Lemma lem6935405 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935406 {A : Type'} : (term12 A) = (term147 A).
Proof. exact (MK_COMB (@lem6935405 A) (@lem6935404 A)). Qed.
Lemma lem6935561 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6935562 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem6935561 A P Q). Qed.
Lemma lem6935563 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term150 A s f g) = (term151 A s f g).
Proof. exact (@lem6935562 A (term116 A s f g) (term128 A s f g)). Qed.
Lemma lem6935564 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term152 A s f g x) = (term107 A s f g x).
Proof. exact (eq_refl (term152 A s f g x)). Qed.
Lemma lem6935565 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term153 A s f g) = (term116 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935564 A s f g x)). Qed.
Lemma lem6935566 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935567 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term154 A s f g) = (term117 A s f g).
Proof. exact (MK_COMB (@lem6935566 A) (@lem6935565 A s f g)). Qed.
Lemma lem6935568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935569 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term155 A s f g) = (term130 A s f g).
Proof. exact (MK_COMB (@lem6935568) (@lem6935567 A s f g)). Qed.
Lemma lem6935570 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term128 A s f g) = (term128 A s f g).
Proof. exact (eq_refl (term128 A s f g)). Qed.
Lemma lem6935571 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term150 A s f g) = (term132 A s f g).
Proof. exact (MK_COMB (@lem6935569 A s f g) (@lem6935570 A s f g)). Qed.
Lemma lem6935572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935573 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term156 A s f g) = (term157 A s f g).
Proof. exact (MK_COMB (@lem6935572) (@lem6935571 A s f g)). Qed.
Lemma lem6935574 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term152 A s f g x) = (term107 A s f g x).
Proof. exact (eq_refl (term152 A s f g x)). Qed.
Lemma lem6935575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935576 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term158 A s f g x) = (term159 A s f g x).
Proof. exact (MK_COMB (@lem6935575) (@lem6935574 A s f g x)). Qed.
Lemma lem6935577 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term128 A s f g) = (term128 A s f g).
Proof. exact (eq_refl (term128 A s f g)). Qed.
Lemma lem6935578 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term160 A x s f g) = (term161 A x s f g).
Proof. exact (MK_COMB (@lem6935576 A s f g x) (@lem6935577 A s f g)). Qed.
Lemma lem6935579 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term162 A s f g) = (term163 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935578 A x s f g)). Qed.
Lemma lem6935580 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935581 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term151 A s f g) = (term164 A s f g).
Proof. exact (MK_COMB (@lem6935580 A) (@lem6935579 A s f g)). Qed.
Lemma lem6935582 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : ((term150 A s f g) = (term151 A s f g)) = ((term132 A s f g) = (term164 A s f g)).
Proof. exact (MK_COMB (@lem6935573 A s f g) (@lem6935581 A s f g)). Qed.
Lemma lem6935583 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term132 A s f g) = (term164 A s f g).
Proof. exact (EQ_MP (@lem6935582 A s f g) (@lem6935563 A s f g)). Qed.
Lemma lem6935584 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem6935585 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term136 A s f g) = (term165 A s f g).
Proof. exact (MK_COMB (@lem6935584 A s) (@lem6935583 A s f g)). Qed.
Lemma lem6935587 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6935588 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (@lem6935587 A P Q). Qed.
Lemma lem6935589 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term168 A s f g) = (term169 A s f g).
Proof. exact (@lem6935588 A (term170 A s) (term163 A s f g)). Qed.
Lemma lem6935590 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term171 A s f g x) = (term161 A x s f g).
Proof. exact (eq_refl (term171 A s f g x)). Qed.
Lemma lem6935591 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term172 A s f g) = (term163 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935590 A x s f g)). Qed.
Lemma lem6935592 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935593 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term173 A s f g) = (term164 A s f g).
Proof. exact (MK_COMB (@lem6935592 A) (@lem6935591 A s f g)). Qed.
Lemma lem6935594 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem6935595 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term168 A s f g) = (term165 A s f g).
Proof. exact (MK_COMB (@lem6935594 A s) (@lem6935593 A s f g)). Qed.
Lemma lem6935596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935597 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term174 A s f g) = (term175 A s f g).
Proof. exact (MK_COMB (@lem6935596) (@lem6935595 A s f g)). Qed.
Lemma lem6935598 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term171 A s f g x) = (term161 A x s f g).
Proof. exact (eq_refl (term171 A s f g x)). Qed.
Lemma lem6935599 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem6935600 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term176 A s f g x) = (term177 A x s f g).
Proof. exact (MK_COMB (@lem6935599 A s) (@lem6935598 A x s f g)). Qed.
Lemma lem6935601 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term179 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935600 A x s f g)). Qed.
Lemma lem6935602 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935603 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term169 A s f g) = (term180 A s f g).
Proof. exact (MK_COMB (@lem6935602 A) (@lem6935601 A s f g)). Qed.
Lemma lem6935604 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : ((term168 A s f g) = (term169 A s f g)) = ((term165 A s f g) = (term180 A s f g)).
Proof. exact (MK_COMB (@lem6935597 A s f g) (@lem6935603 A s f g)). Qed.
Lemma lem6935605 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term165 A s f g) = (term180 A s f g).
Proof. exact (EQ_MP (@lem6935604 A s f g) (@lem6935589 A s f g)). Qed.
Lemma lem6935606 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term136 A s f g) = (term180 A s f g).
Proof. exact (TRANS (@lem6935585 A s f g) (@lem6935605 A s f g)). Qed.
Lemma lem6935607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935608 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term139 A s f g) = (term181 A s f g).
Proof. exact (MK_COMB (@lem6935607) (@lem6935606 A s f g)). Qed.
Lemma lem6935609 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem6935610 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term141 A f s g) = (term182 A f s g).
Proof. exact (MK_COMB (@lem6935608 A s f g) (@lem6935609 A f s g)). Qed.
Lemma lem6935612 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6935613 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem6935612 A P Q). Qed.
Lemma lem6935614 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term183 A f s g) = (term184 A f s g).
Proof. exact (@lem6935613 A (term179 A s f g) (term39 A f s g)). Qed.
Lemma lem6935615 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term185 A s f g x) = (term177 A x s f g).
Proof. exact (eq_refl (term185 A s f g x)). Qed.
Lemma lem6935616 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term186 A s f g) = (term179 A s f g).
Proof. exact (fun_ext (fun x : A => @lem6935615 A x s f g)). Qed.
Lemma lem6935617 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935618 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term187 A s f g) = (term180 A s f g).
Proof. exact (MK_COMB (@lem6935617 A) (@lem6935616 A s f g)). Qed.
Lemma lem6935619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935620 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term188 A s f g) = (term181 A s f g).
Proof. exact (MK_COMB (@lem6935619) (@lem6935618 A s f g)). Qed.
Lemma lem6935621 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem6935622 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term183 A f s g) = (term182 A f s g).
Proof. exact (MK_COMB (@lem6935620 A s f g) (@lem6935621 A f s g)). Qed.
Lemma lem6935623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935624 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term189 A f s g) = (term190 A f s g).
Proof. exact (MK_COMB (@lem6935623) (@lem6935622 A f s g)). Qed.
Lemma lem6935625 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term185 A s f g x) = (term177 A x s f g).
Proof. exact (eq_refl (term185 A s f g x)). Qed.
Lemma lem6935626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935627 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term191 A s f g x) = (term192 A x s f g).
Proof. exact (MK_COMB (@lem6935626) (@lem6935625 A x s f g)). Qed.
Lemma lem6935628 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem6935629 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term193 A x f s g) = (term194 A x f s g).
Proof. exact (MK_COMB (@lem6935627 A x s f g) (@lem6935628 A f s g)). Qed.
Lemma lem6935630 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term195 A f s g) = (term196 A f s g).
Proof. exact (fun_ext (fun x : A => @lem6935629 A x f s g)). Qed.
Lemma lem6935631 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935632 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term184 A f s g) = (term197 A f s g).
Proof. exact (MK_COMB (@lem6935631 A) (@lem6935630 A f s g)). Qed.
Lemma lem6935633 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term183 A f s g) = (term184 A f s g)) = ((term182 A f s g) = (term197 A f s g)).
Proof. exact (MK_COMB (@lem6935624 A f s g) (@lem6935632 A f s g)). Qed.
Lemma lem6935634 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term182 A f s g) = (term197 A f s g).
Proof. exact (EQ_MP (@lem6935633 A f s g) (@lem6935614 A f s g)). Qed.
Lemma lem6935635 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term141 A f s g) = (term197 A f s g).
Proof. exact (TRANS (@lem6935610 A f s g) (@lem6935634 A f s g)). Qed.
Lemma lem6935636 {A : Type'} (f : A -> nat) (g : A -> nat) : (term142 A f g) = (term198 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6935635 A f s g)). Qed.
Lemma lem6935637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6935638 {A : Type'} (f : A -> nat) (g : A -> nat) : (term143 A f g) = (term199 A f g).
Proof. exact (MK_COMB (@lem6935637 A) (@lem6935636 A f g)). Qed.
Lemma lem6935640 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935641 {A : Type'} (P : type672 A) : (term202 A P) = (term203 A P).
Proof. exact (@lem6935640 (A -> Prop) A P). Qed.
Lemma lem6935642 {A : Type'} (f : A -> nat) (g : A -> nat) : (term204 A f g) = (term205 A f g).
Proof. exact (@lem6935641 A (term206 A f g)). Qed.
Lemma lem6935643 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term207 A f g s) = (term196 A f s g).
Proof. exact (eq_refl (term207 A f g s)). Qed.
Lemma lem6935644 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935645 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term208 A f g s x) = (term209 A f s g x).
Proof. exact (MK_COMB (@lem6935643 A f s g) (@lem6935644 A x)). Qed.
Lemma lem6935646 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term209 A f s g x) = (term194 A x f s g).
Proof. exact (eq_refl (term209 A f s g x)). Qed.
Lemma lem6935647 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term208 A f g s x) = (term194 A x f s g).
Proof. exact (TRANS (@lem6935645 A f s g x) (@lem6935646 A x f s g)). Qed.
Lemma lem6935648 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term210 A f g s) = (term196 A f s g).
Proof. exact (fun_ext (fun x : A => @lem6935647 A x f s g)). Qed.
Lemma lem6935649 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6935650 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term211 A f g s) = (term197 A f s g).
Proof. exact (MK_COMB (@lem6935649 A) (@lem6935648 A f s g)). Qed.
Lemma lem6935651 {A : Type'} (f : A -> nat) (g : A -> nat) : (term212 A f g) = (term198 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6935650 A f s g)). Qed.
Lemma lem6935652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6935653 {A : Type'} (f : A -> nat) (g : A -> nat) : (term204 A f g) = (term199 A f g).
Proof. exact (MK_COMB (@lem6935652 A) (@lem6935651 A f g)). Qed.
Lemma lem6935654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935655 {A : Type'} (f : A -> nat) (g : A -> nat) : (term213 A f g) = (term214 A f g).
Proof. exact (MK_COMB (@lem6935654) (@lem6935653 A f g)). Qed.
Lemma lem6935656 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term207 A f g s) = (term196 A f s g).
Proof. exact (eq_refl (term207 A f g s)). Qed.
Lemma lem6935657 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6935658 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type684 A) (s : A -> Prop) : (term215 A f g x s) = (term216 A f g x s).
Proof. exact (MK_COMB (@lem6935656 A f s g) (@lem6935657 A x s)). Qed.
Lemma lem6935659 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term216 A f g x s) = (term217 A x f s g).
Proof. exact (eq_refl (term216 A f g x s)). Qed.
Lemma lem6935660 {A : Type'} (x : type684 A) (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term215 A f g x s) = (term217 A x f s g).
Proof. exact (TRANS (@lem6935658 A f g x s) (@lem6935659 A x f s g)). Qed.
Lemma lem6935661 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term218 A f g x) = (term219 A x f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6935660 A x f s g)). Qed.
Lemma lem6935662 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6935663 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term220 A f g x) = (term221 A x f g).
Proof. exact (MK_COMB (@lem6935662 A) (@lem6935661 A x f g)). Qed.
Lemma lem6935664 {A : Type'} (f : A -> nat) (g : A -> nat) : (term222 A f g) = (term223 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem6935663 A x f g)). Qed.
Lemma lem6935665 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6935666 {A : Type'} (f : A -> nat) (g : A -> nat) : (term205 A f g) = (term224 A f g).
Proof. exact (MK_COMB (@lem6935665 A) (@lem6935664 A f g)). Qed.
Lemma lem6935667 {A : Type'} (f : A -> nat) (g : A -> nat) : ((term204 A f g) = (term205 A f g)) = ((term199 A f g) = (term224 A f g)).
Proof. exact (MK_COMB (@lem6935655 A f g) (@lem6935666 A f g)). Qed.
Lemma lem6935668 {A : Type'} (f : A -> nat) (g : A -> nat) : (term199 A f g) = (term224 A f g).
Proof. exact (EQ_MP (@lem6935667 A f g) (@lem6935642 A f g)). Qed.
Lemma lem6935669 {A : Type'} (f : A -> nat) (g : A -> nat) : (term143 A f g) = (term224 A f g).
Proof. exact (TRANS (@lem6935638 A f g) (@lem6935668 A f g)). Qed.
Lemma lem6935670 {A : Type'} (f : A -> nat) : (term144 A f) = (term225 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6935669 A f g)). Qed.
Lemma lem6935671 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935672 {A : Type'} (f : A -> nat) : (term145 A f) = (term226 A f).
Proof. exact (MK_COMB (@lem6935671 A) (@lem6935670 A f)). Qed.
Lemma lem6935674 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935675 {A : Type'} (P : type690 A) : (term227 A P) = (term228 A P).
Proof. exact (@lem6935674 (A -> nat) (type684 A) P). Qed.
Lemma lem6935676 {A : Type'} (f : A -> nat) : (term229 A f) = (term230 A f).
Proof. exact (@lem6935675 A (term231 A f)). Qed.
Lemma lem6935677 {A : Type'} (f : A -> nat) (g : A -> nat) : (term232 A f g) = (term223 A f g).
Proof. exact (eq_refl (term232 A f g)). Qed.
Lemma lem6935678 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935679 {A : Type'} (f : A -> nat) (g : A -> nat) (x : type684 A) : (term233 A f g x) = (term234 A f g x).
Proof. exact (MK_COMB (@lem6935677 A f g) (@lem6935678 A x)). Qed.
Lemma lem6935680 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term234 A f g x) = (term221 A x f g).
Proof. exact (eq_refl (term234 A f g x)). Qed.
Lemma lem6935681 {A : Type'} (x : type684 A) (f : A -> nat) (g : A -> nat) : (term233 A f g x) = (term221 A x f g).
Proof. exact (TRANS (@lem6935679 A f g x) (@lem6935680 A x f g)). Qed.
Lemma lem6935682 {A : Type'} (f : A -> nat) (g : A -> nat) : (term235 A f g) = (term223 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem6935681 A x f g)). Qed.
Lemma lem6935683 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6935684 {A : Type'} (f : A -> nat) (g : A -> nat) : (term236 A f g) = (term224 A f g).
Proof. exact (MK_COMB (@lem6935683 A) (@lem6935682 A f g)). Qed.
Lemma lem6935685 {A : Type'} (f : A -> nat) : (term237 A f) = (term225 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6935684 A f g)). Qed.
Lemma lem6935686 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935687 {A : Type'} (f : A -> nat) : (term229 A f) = (term226 A f).
Proof. exact (MK_COMB (@lem6935686 A) (@lem6935685 A f)). Qed.
Lemma lem6935688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935689 {A : Type'} (f : A -> nat) : (term238 A f) = (term239 A f).
Proof. exact (MK_COMB (@lem6935688) (@lem6935687 A f)). Qed.
Lemma lem6935690 {A : Type'} (f : A -> nat) (g : A -> nat) : (term232 A f g) = (term223 A f g).
Proof. exact (eq_refl (term232 A f g)). Qed.
Lemma lem6935691 {A : Type'} (x : type694 A) (g : A -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem6935692 {A : Type'} (f : A -> nat) (x : type694 A) (g : A -> nat) : (term240 A f x g) = (term241 A f x g).
Proof. exact (MK_COMB (@lem6935690 A f g) (@lem6935691 A x g)). Qed.
Lemma lem6935693 {A : Type'} (x : type694 A) (f : A -> nat) (g : A -> nat) : (term241 A f x g) = (term242 A x f g).
Proof. exact (eq_refl (term241 A f x g)). Qed.
Lemma lem6935694 {A : Type'} (x : type694 A) (f : A -> nat) (g : A -> nat) : (term240 A f x g) = (term242 A x f g).
Proof. exact (TRANS (@lem6935692 A f x g) (@lem6935693 A x f g)). Qed.
Lemma lem6935695 {A : Type'} (x : type694 A) (f : A -> nat) : (term243 A f x) = (term244 A x f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6935694 A x f g)). Qed.
Lemma lem6935696 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935697 {A : Type'} (x : type694 A) (f : A -> nat) : (term245 A f x) = (term246 A x f).
Proof. exact (MK_COMB (@lem6935696 A) (@lem6935695 A x f)). Qed.
Lemma lem6935698 {A : Type'} (f : A -> nat) : (term247 A f) = (term248 A f).
Proof. exact (fun_ext (fun x : type694 A => @lem6935697 A x f)). Qed.
Lemma lem6935699 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6935700 {A : Type'} (f : A -> nat) : (term230 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem6935699 A) (@lem6935698 A f)). Qed.
Lemma lem6935701 {A : Type'} (f : A -> nat) : ((term229 A f) = (term230 A f)) = ((term226 A f) = (term249 A f)).
Proof. exact (MK_COMB (@lem6935689 A f) (@lem6935700 A f)). Qed.
Lemma lem6935702 {A : Type'} (f : A -> nat) : (term226 A f) = (term249 A f).
Proof. exact (EQ_MP (@lem6935701 A f) (@lem6935676 A f)). Qed.
Lemma lem6935703 {A : Type'} (f : A -> nat) : (term145 A f) = (term249 A f).
Proof. exact (TRANS (@lem6935672 A f) (@lem6935702 A f)). Qed.
Lemma lem6935704 {A : Type'} : (term146 A) = (term250 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6935703 A f)). Qed.
Lemma lem6935705 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935706 {A : Type'} : (term147 A) = (term251 A).
Proof. exact (MK_COMB (@lem6935705 A) (@lem6935704 A)). Qed.
Lemma lem6935708 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6935709 {A : Type'} (P : type691 A) : (term252 A P) = (term253 A P).
Proof. exact (@lem6935708 (A -> nat) (type694 A) P). Qed.
Lemma lem6935710 {A : Type'} : (term254 A) = (term255 A).
Proof. exact (@lem6935709 A (term256 A)). Qed.
Lemma lem6935711 {A : Type'} (f : A -> nat) : (term257 A f) = (term248 A f).
Proof. exact (eq_refl (term257 A f)). Qed.
Lemma lem6935712 {A : Type'} (x : type694 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6935713 {A : Type'} (f : A -> nat) (x : type694 A) : (term258 A f x) = (term259 A f x).
Proof. exact (MK_COMB (@lem6935711 A f) (@lem6935712 A x)). Qed.
Lemma lem6935714 {A : Type'} (x : type694 A) (f : A -> nat) : (term259 A f x) = (term246 A x f).
Proof. exact (eq_refl (term259 A f x)). Qed.
Lemma lem6935715 {A : Type'} (x : type694 A) (f : A -> nat) : (term258 A f x) = (term246 A x f).
Proof. exact (TRANS (@lem6935713 A f x) (@lem6935714 A x f)). Qed.
Lemma lem6935716 {A : Type'} (f : A -> nat) : (term260 A f) = (term248 A f).
Proof. exact (fun_ext (fun x : type694 A => @lem6935715 A x f)). Qed.
Lemma lem6935717 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6935718 {A : Type'} (f : A -> nat) : (term261 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem6935717 A) (@lem6935716 A f)). Qed.
Lemma lem6935719 {A : Type'} : (term262 A) = (term250 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6935718 A f)). Qed.
Lemma lem6935720 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935721 {A : Type'} : (term254 A) = (term251 A).
Proof. exact (MK_COMB (@lem6935720 A) (@lem6935719 A)). Qed.
Lemma lem6935722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935723 {A : Type'} : (term263 A) = (term264 A).
Proof. exact (MK_COMB (@lem6935722) (@lem6935721 A)). Qed.
Lemma lem6935724 {A : Type'} (f : A -> nat) : (term257 A f) = (term248 A f).
Proof. exact (eq_refl (term257 A f)). Qed.
Lemma lem6935725 {A : Type'} (x : type695 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6935726 {A : Type'} (x : type695 A) (f : A -> nat) : (term265 A x f) = (term266 A x f).
Proof. exact (MK_COMB (@lem6935724 A f) (@lem6935725 A x f)). Qed.
Lemma lem6935727 {A : Type'} (x : type695 A) (f : A -> nat) : (term266 A x f) = (term267 A x f).
Proof. exact (eq_refl (term266 A x f)). Qed.
Lemma lem6935728 {A : Type'} (x : type695 A) (f : A -> nat) : (term265 A x f) = (term267 A x f).
Proof. exact (TRANS (@lem6935726 A x f) (@lem6935727 A x f)). Qed.
Lemma lem6935729 {A : Type'} (x : type695 A) : (term268 A x) = (term269 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6935728 A x f)). Qed.
Lemma lem6935730 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6935731 {A : Type'} (x : type695 A) : (term270 A x) = (term271 A x).
Proof. exact (MK_COMB (@lem6935730 A) (@lem6935729 A x)). Qed.
Lemma lem6935732 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (fun_ext (fun x : type695 A => @lem6935731 A x)). Qed.
Lemma lem6935733 {A : Type'} : (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> nat) -> (A -> Prop) -> A))). Qed.
Lemma lem6935734 {A : Type'} : (term255 A) = (term274 A).
Proof. exact (MK_COMB (@lem6935733 A) (@lem6935732 A)). Qed.
Lemma lem6935735 {A : Type'} : ((term254 A) = (term255 A)) = ((term251 A) = (term274 A)).
Proof. exact (MK_COMB (@lem6935723 A) (@lem6935734 A)). Qed.
Lemma lem6935736 {A : Type'} : (term251 A) = (term274 A).
Proof. exact (EQ_MP (@lem6935735 A) (@lem6935710 A)). Qed.
Lemma lem6935738 {A : Type'} : (term147 A) = (term274 A).
Proof. exact (TRANS (@lem6935706 A) (@lem6935736 A)). Qed.
Lemma lem6935739 {A : Type'} : (term12 A) = (term274 A).
Proof. exact (TRANS (@lem6935406 A) (@lem6935738 A)). Qed.
Lemma lem6935740 {A : Type'} (h1 : term12 A) : term274 A.
Proof. exact (EQ_MP (@lem6935739 A) (@lem6934787 A h1)). Qed.
Lemma lem6935747 (m : nat) (n : nat) : (term34 m n) = (term275 m n).
Proof. exact (@lem17265 (Peano.lt m n) (Peano.le m n)). Qed.
Lemma lem6935748 (m : nat) : (term35 m) = (term276 m).
Proof. exact (fun_ext (fun n : nat => @lem6935747 m n)). Qed.
Lemma lem6935749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6935750 (m : nat) : (term36 m) = (term277 m).
Proof. exact (MK_COMB (@lem6935749) (@lem6935748 m)). Qed.
Lemma lem6935751 : term37 = term278.
Proof. exact (fun_ext (fun m : nat => @lem6935750 m)). Qed.
Lemma lem6935752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6935809 : term38 = term279.
Proof. exact (MK_COMB (@lem6935752) (@lem6935751)). Qed.
Lemma lem6935810 (h1 : term38) : term279.
Proof. exact (EQ_MP (@lem6935809) (@lem6934788 h1)). Qed.
Lemma lem6935812 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (@IN _127128 x s).
Proof. exact (eq_refl (@IN _127128 x s)). Qed.
Lemma lem6935813 {_127128 : Type'} (P : _127128 -> Prop) : (term120 _127128 P) = (term121 _127128 P).
Proof. exact (@lem18394 _127128 P). Qed.
Lemma lem6935814 {_127128 : Type'} (s : _127128 -> Prop) : (term280 _127128 s) = (term281 _127128 s).
Proof. exact (@lem6935813 _127128 (term30 _127128 s)). Qed.
Lemma lem6935815 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term282 _127128 s x) = (@IN _127128 x s).
Proof. exact (eq_refl (term282 _127128 s x)). Qed.
Lemma lem6935816 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6935818 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term283 _127128 s x) = (term284 _127128 x s).
Proof. exact (MK_COMB (@lem6935816) (@lem6935815 _127128 x s)). Qed.
Lemma lem6935819 {_127128 : Type'} (s : _127128 -> Prop) : (term285 _127128 s) = (term286 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6935818 _127128 x s)). Qed.
Lemma lem6935820 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6935821 {_127128 : Type'} (s : _127128 -> Prop) : (term281 _127128 s) = (term287 _127128 s).
Proof. exact (MK_COMB (@lem6935820 _127128) (@lem6935819 _127128 s)). Qed.
Lemma lem6935822 {_127128 : Type'} (s : _127128 -> Prop) : (term280 _127128 s) = (term287 _127128 s).
Proof. exact (TRANS (@lem6935814 _127128 s) (@lem6935821 _127128 s)). Qed.
Lemma lem6935823 {_127128 : Type'} (s : _127128 -> Prop) : (term30 _127128 s) = (term30 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6935812 _127128 x s)). Qed.
Lemma lem6935824 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935825 {_127128 : Type'} (s : _127128 -> Prop) : (term31 _127128 s) = (term31 _127128 s).
Proof. exact (MK_COMB (@lem6935824 _127128) (@lem6935823 _127128 s)). Qed.
Lemma lem6935826 {_127128 : Type'} (s : _127128 -> Prop) : (term29 _127128 s) = (term29 _127128 s).
Proof. exact (eq_refl (term29 _127128 s)). Qed.
Lemma lem6935829 {_127128 : Type'} (s : _127128 -> Prop) : (term288 _127128 s) = (s = (@EMPTY _127128)).
Proof. exact (@lem16933 (s = (@EMPTY _127128))). Qed.
Lemma lem6935830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935831 {_127128 : Type'} (s : _127128 -> Prop) : (term289 _127128 s) = (term290 _127128 s).
Proof. exact (MK_COMB (@lem6935830) (@lem6935822 _127128 s)). Qed.
Lemma lem6935832 {_127128 : Type'} (s : _127128 -> Prop) : (term291 _127128 s) = (term292 _127128 s).
Proof. exact (MK_COMB (@lem6935831 _127128 s) (@lem6935826 _127128 s)). Qed.
Lemma lem6935833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935834 {_127128 : Type'} (s : _127128 -> Prop) : (term293 _127128 s) = (term293 _127128 s).
Proof. exact (MK_COMB (@lem6935833) (@lem6935825 _127128 s)). Qed.
Lemma lem6935835 {_127128 : Type'} (s : _127128 -> Prop) : (term294 _127128 s) = (term295 _127128 s).
Proof. exact (MK_COMB (@lem6935834 _127128 s) (@lem6935829 _127128 s)). Qed.
Lemma lem6935836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6935837 {_127128 : Type'} (s : _127128 -> Prop) : (term296 _127128 s) = (term297 _127128 s).
Proof. exact (MK_COMB (@lem6935836) (@lem6935835 _127128 s)). Qed.
Lemma lem6935838 {_127128 : Type'} (s : _127128 -> Prop) : (term298 _127128 s) = (term299 _127128 s).
Proof. exact (MK_COMB (@lem6935837 _127128 s) (@lem6935832 _127128 s)). Qed.
Lemma lem6935839 {_127128 : Type'} (s : _127128 -> Prop) : ((term31 _127128 s) = (term29 _127128 s)) = (term298 _127128 s).
Proof. exact (@lem17784 (term31 _127128 s) (term29 _127128 s)). Qed.
Lemma lem6935840 {_127128 : Type'} (s : _127128 -> Prop) : ((term31 _127128 s) = (term29 _127128 s)) = (term299 _127128 s).
Proof. exact (TRANS (@lem6935839 _127128 s) (@lem6935838 _127128 s)). Qed.
Lemma lem6935841 {_127128 : Type'} : (term33 _127128) = (term300 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935840 _127128 s)). Qed.
Lemma lem6935842 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935843 {_127128 : Type'} : (term11 _127128) = (term301 _127128).
Proof. exact (MK_COMB (@lem6935842 _127128) (@lem6935841 _127128)). Qed.
Lemma lem6935845 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6935846 {_127128 : Type'} (P : type686 _127128) (Q : type686 _127128) : (term304 _127128 P Q) = (term305 _127128 P Q).
Proof. exact (@lem6935845 (_127128 -> Prop) P Q). Qed.
Lemma lem6935847 {_127128 : Type'} : (term306 _127128) = (term307 _127128).
Proof. exact (@lem6935846 _127128 (term308 _127128) (term309 _127128)). Qed.
Lemma lem6935848 {_127128 : Type'} (s : _127128 -> Prop) : (term310 _127128 s) = (term295 _127128 s).
Proof. exact (eq_refl (term310 _127128 s)). Qed.
Lemma lem6935849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6935850 {_127128 : Type'} (s : _127128 -> Prop) : (term311 _127128 s) = (term297 _127128 s).
Proof. exact (MK_COMB (@lem6935849) (@lem6935848 _127128 s)). Qed.
Lemma lem6935851 {_127128 : Type'} (s : _127128 -> Prop) : (term312 _127128 s) = (term292 _127128 s).
Proof. exact (eq_refl (term312 _127128 s)). Qed.
Lemma lem6935852 {_127128 : Type'} (s : _127128 -> Prop) : (term313 _127128 s) = (term299 _127128 s).
Proof. exact (MK_COMB (@lem6935850 _127128 s) (@lem6935851 _127128 s)). Qed.
Lemma lem6935853 {_127128 : Type'} : (term314 _127128) = (term300 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935852 _127128 s)). Qed.
Lemma lem6935854 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935855 {_127128 : Type'} : (term306 _127128) = (term301 _127128).
Proof. exact (MK_COMB (@lem6935854 _127128) (@lem6935853 _127128)). Qed.
Lemma lem6935856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935857 {_127128 : Type'} : (term315 _127128) = (term316 _127128).
Proof. exact (MK_COMB (@lem6935856) (@lem6935855 _127128)). Qed.
Lemma lem6935858 {_127128 : Type'} (s : _127128 -> Prop) : (term310 _127128 s) = (term295 _127128 s).
Proof. exact (eq_refl (term310 _127128 s)). Qed.
Lemma lem6935859 {_127128 : Type'} : (term317 _127128) = (term308 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935858 _127128 s)). Qed.
Lemma lem6935860 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935861 {_127128 : Type'} : (term318 _127128) = (term319 _127128).
Proof. exact (MK_COMB (@lem6935860 _127128) (@lem6935859 _127128)). Qed.
Lemma lem6935862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6935863 {_127128 : Type'} : (term320 _127128) = (term321 _127128).
Proof. exact (MK_COMB (@lem6935862) (@lem6935861 _127128)). Qed.
Lemma lem6935864 {_127128 : Type'} (s : _127128 -> Prop) : (term312 _127128 s) = (term292 _127128 s).
Proof. exact (eq_refl (term312 _127128 s)). Qed.
Lemma lem6935865 {_127128 : Type'} : (term322 _127128) = (term309 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935864 _127128 s)). Qed.
Lemma lem6935866 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6935867 {_127128 : Type'} : (term323 _127128) = (term324 _127128).
Proof. exact (MK_COMB (@lem6935866 _127128) (@lem6935865 _127128)). Qed.
Lemma lem6935868 {_127128 : Type'} : (term307 _127128) = (term325 _127128).
Proof. exact (MK_COMB (@lem6935863 _127128) (@lem6935867 _127128)). Qed.
Lemma lem6935869 {_127128 : Type'} : ((term306 _127128) = (term307 _127128)) = ((term301 _127128) = (term325 _127128)).
Proof. exact (MK_COMB (@lem6935857 _127128) (@lem6935868 _127128)). Qed.
Lemma lem6935870 {_127128 : Type'} : (term301 _127128) = (term325 _127128).
Proof. exact (EQ_MP (@lem6935869 _127128) (@lem6935847 _127128)). Qed.
Lemma lem6935976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6935977 {_127128 : Type'} (P : _127128 -> Prop) (Q : Prop) : (term148 _127128 P Q) = (term149 _127128 P Q).
Proof. exact (@lem6935976 _127128 P Q). Qed.
Lemma lem6935978 {_127128 : Type'} (s : _127128 -> Prop) : (term326 _127128 s) = (term327 _127128 s).
Proof. exact (@lem6935977 _127128 (term30 _127128 s) (s = (@EMPTY _127128))). Qed.
Lemma lem6935979 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term282 _127128 s x) = (@IN _127128 x s).
Proof. exact (eq_refl (term282 _127128 s x)). Qed.
Lemma lem6935980 {_127128 : Type'} (s : _127128 -> Prop) : (term328 _127128 s) = (term30 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6935979 _127128 x s)). Qed.
Lemma lem6935981 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935982 {_127128 : Type'} (s : _127128 -> Prop) : (term329 _127128 s) = (term31 _127128 s).
Proof. exact (MK_COMB (@lem6935981 _127128) (@lem6935980 _127128 s)). Qed.
Lemma lem6935983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935984 {_127128 : Type'} (s : _127128 -> Prop) : (term330 _127128 s) = (term293 _127128 s).
Proof. exact (MK_COMB (@lem6935983) (@lem6935982 _127128 s)). Qed.
Lemma lem6935985 {_127128 : Type'} (s : _127128 -> Prop) : (s = (@EMPTY _127128)) = (s = (@EMPTY _127128)).
Proof. exact (eq_refl (s = (@EMPTY _127128))). Qed.
Lemma lem6935986 {_127128 : Type'} (s : _127128 -> Prop) : (term326 _127128 s) = (term295 _127128 s).
Proof. exact (MK_COMB (@lem6935984 _127128 s) (@lem6935985 _127128 s)). Qed.
Lemma lem6935987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6935988 {_127128 : Type'} (s : _127128 -> Prop) : (term331 _127128 s) = (term332 _127128 s).
Proof. exact (MK_COMB (@lem6935987) (@lem6935986 _127128 s)). Qed.
Lemma lem6935989 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term282 _127128 s x) = (@IN _127128 x s).
Proof. exact (eq_refl (term282 _127128 s x)). Qed.
Lemma lem6935990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6935991 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term333 _127128 s x) = (term334 _127128 x s).
Proof. exact (MK_COMB (@lem6935990) (@lem6935989 _127128 x s)). Qed.
Lemma lem6935992 {_127128 : Type'} (s : _127128 -> Prop) : (s = (@EMPTY _127128)) = (s = (@EMPTY _127128)).
Proof. exact (eq_refl (s = (@EMPTY _127128))). Qed.
Lemma lem6935993 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term335 _127128 x s) = (term336 _127128 x s).
Proof. exact (MK_COMB (@lem6935991 _127128 x s) (@lem6935992 _127128 s)). Qed.
Lemma lem6935994 {_127128 : Type'} (s : _127128 -> Prop) : (term337 _127128 s) = (term338 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6935993 _127128 x s)). Qed.
Lemma lem6935995 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6935996 {_127128 : Type'} (s : _127128 -> Prop) : (term327 _127128 s) = (term339 _127128 s).
Proof. exact (MK_COMB (@lem6935995 _127128) (@lem6935994 _127128 s)). Qed.
Lemma lem6935997 {_127128 : Type'} (s : _127128 -> Prop) : ((term326 _127128 s) = (term327 _127128 s)) = ((term295 _127128 s) = (term339 _127128 s)).
Proof. exact (MK_COMB (@lem6935988 _127128 s) (@lem6935996 _127128 s)). Qed.
Lemma lem6935998 {_127128 : Type'} (s : _127128 -> Prop) : (term295 _127128 s) = (term339 _127128 s).
Proof. exact (EQ_MP (@lem6935997 _127128 s) (@lem6935978 _127128 s)). Qed.
Lemma lem6935999 {_127128 : Type'} : (term308 _127128) = (term340 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6935998 _127128 s)). Qed.
Lemma lem6936000 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936001 {_127128 : Type'} : (term319 _127128) = (term341 _127128).
Proof. exact (MK_COMB (@lem6936000 _127128) (@lem6935999 _127128)). Qed.
Lemma lem6936003 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6936004 {_127128 : Type'} (P : type672 _127128) : (term202 _127128 P) = (term203 _127128 P).
Proof. exact (@lem6936003 (_127128 -> Prop) _127128 P). Qed.
Lemma lem6936005 {_127128 : Type'} : (term342 _127128) = (term343 _127128).
Proof. exact (@lem6936004 _127128 (term344 _127128)). Qed.
Lemma lem6936006 {_127128 : Type'} (s : _127128 -> Prop) : (term345 _127128 s) = (term338 _127128 s).
Proof. exact (eq_refl (term345 _127128 s)). Qed.
Lemma lem6936007 {_127128 : Type'} (x : _127128) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6936008 {_127128 : Type'} (s : _127128 -> Prop) (x : _127128) : (term346 _127128 s x) = (term347 _127128 s x).
Proof. exact (MK_COMB (@lem6936006 _127128 s) (@lem6936007 _127128 x)). Qed.
Lemma lem6936009 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term347 _127128 s x) = (term336 _127128 x s).
Proof. exact (eq_refl (term347 _127128 s x)). Qed.
Lemma lem6936010 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term346 _127128 s x) = (term336 _127128 x s).
Proof. exact (TRANS (@lem6936008 _127128 s x) (@lem6936009 _127128 x s)). Qed.
Lemma lem6936011 {_127128 : Type'} (s : _127128 -> Prop) : (term348 _127128 s) = (term338 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6936010 _127128 x s)). Qed.
Lemma lem6936012 {_127128 : Type'} : (@ex _127128) = (@ex _127128).
Proof. exact (eq_refl (@ex _127128)). Qed.
Lemma lem6936013 {_127128 : Type'} (s : _127128 -> Prop) : (term349 _127128 s) = (term339 _127128 s).
Proof. exact (MK_COMB (@lem6936012 _127128) (@lem6936011 _127128 s)). Qed.
Lemma lem6936014 {_127128 : Type'} : (term350 _127128) = (term340 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6936013 _127128 s)). Qed.
Lemma lem6936015 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936016 {_127128 : Type'} : (term342 _127128) = (term341 _127128).
Proof. exact (MK_COMB (@lem6936015 _127128) (@lem6936014 _127128)). Qed.
Lemma lem6936017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6936018 {_127128 : Type'} : (term351 _127128) = (term352 _127128).
Proof. exact (MK_COMB (@lem6936017) (@lem6936016 _127128)). Qed.
Lemma lem6936019 {_127128 : Type'} (s : _127128 -> Prop) : (term345 _127128 s) = (term338 _127128 s).
Proof. exact (eq_refl (term345 _127128 s)). Qed.
Lemma lem6936020 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6936021 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term353 _127128 x s) = (term354 _127128 x s).
Proof. exact (MK_COMB (@lem6936019 _127128 s) (@lem6936020 _127128 x s)). Qed.
Lemma lem6936022 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term354 _127128 x s) = (term355 _127128 x s).
Proof. exact (eq_refl (term354 _127128 x s)). Qed.
Lemma lem6936023 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term353 _127128 x s) = (term355 _127128 x s).
Proof. exact (TRANS (@lem6936021 _127128 x s) (@lem6936022 _127128 x s)). Qed.
Lemma lem6936024 {_127128 : Type'} (x : type684 _127128) : (term356 _127128 x) = (term357 _127128 x).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6936023 _127128 x s)). Qed.
Lemma lem6936025 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936026 {_127128 : Type'} (x : type684 _127128) : (term358 _127128 x) = (term359 _127128 x).
Proof. exact (MK_COMB (@lem6936025 _127128) (@lem6936024 _127128 x)). Qed.
Lemma lem6936027 {_127128 : Type'} : (term360 _127128) = (term361 _127128).
Proof. exact (fun_ext (fun x : type684 _127128 => @lem6936026 _127128 x)). Qed.
Lemma lem6936028 {_127128 : Type'} : (@ex ((_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> Prop) -> _127128))). Qed.
Lemma lem6936029 {_127128 : Type'} : (term343 _127128) = (term362 _127128).
Proof. exact (MK_COMB (@lem6936028 _127128) (@lem6936027 _127128)). Qed.
Lemma lem6936030 {_127128 : Type'} : ((term342 _127128) = (term343 _127128)) = ((term341 _127128) = (term362 _127128)).
Proof. exact (MK_COMB (@lem6936018 _127128) (@lem6936029 _127128)). Qed.
Lemma lem6936031 {_127128 : Type'} : (term341 _127128) = (term362 _127128).
Proof. exact (EQ_MP (@lem6936030 _127128) (@lem6936005 _127128)). Qed.
Lemma lem6936032 {_127128 : Type'} : (term319 _127128) = (term362 _127128).
Proof. exact (TRANS (@lem6936001 _127128) (@lem6936031 _127128)). Qed.
Lemma lem6936033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936034 {_127128 : Type'} : (term321 _127128) = (term363 _127128).
Proof. exact (MK_COMB (@lem6936033) (@lem6936032 _127128)). Qed.
Lemma lem6936035 {_127128 : Type'} : (term324 _127128) = (term324 _127128).
Proof. exact (eq_refl (term324 _127128)). Qed.
Lemma lem6936036 {_127128 : Type'} : (term325 _127128) = (term364 _127128).
Proof. exact (MK_COMB (@lem6936034 _127128) (@lem6936035 _127128)). Qed.
Lemma lem6936038 {A : Type'} (P : A -> Prop) (Q : Prop) : (term365 A P Q) = (term366 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6936039 {_127128 : Type'} (P : type162 _127128) (Q : Prop) : (term367 _127128 P Q) = (term368 _127128 P Q).
Proof. exact (@lem6936038 (type684 _127128) P Q). Qed.
Lemma lem6936040 {_127128 : Type'} : (term369 _127128) = (term370 _127128).
Proof. exact (@lem6936039 _127128 (term361 _127128) (term324 _127128)). Qed.
Lemma lem6936041 {_127128 : Type'} (x : type684 _127128) : (term371 _127128 x) = (term359 _127128 x).
Proof. exact (eq_refl (term371 _127128 x)). Qed.
Lemma lem6936042 {_127128 : Type'} : (term372 _127128) = (term361 _127128).
Proof. exact (fun_ext (fun x : type684 _127128 => @lem6936041 _127128 x)). Qed.
Lemma lem6936043 {_127128 : Type'} : (@ex ((_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> Prop) -> _127128))). Qed.
Lemma lem6936044 {_127128 : Type'} : (term373 _127128) = (term362 _127128).
Proof. exact (MK_COMB (@lem6936043 _127128) (@lem6936042 _127128)). Qed.
Lemma lem6936045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936046 {_127128 : Type'} : (term374 _127128) = (term363 _127128).
Proof. exact (MK_COMB (@lem6936045) (@lem6936044 _127128)). Qed.
Lemma lem6936047 {_127128 : Type'} : (term324 _127128) = (term324 _127128).
Proof. exact (eq_refl (term324 _127128)). Qed.
Lemma lem6936048 {_127128 : Type'} : (term369 _127128) = (term364 _127128).
Proof. exact (MK_COMB (@lem6936046 _127128) (@lem6936047 _127128)). Qed.
Lemma lem6936049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6936050 {_127128 : Type'} : (term375 _127128) = (term376 _127128).
Proof. exact (MK_COMB (@lem6936049) (@lem6936048 _127128)). Qed.
Lemma lem6936051 {_127128 : Type'} (x : type684 _127128) : (term371 _127128 x) = (term359 _127128 x).
Proof. exact (eq_refl (term371 _127128 x)). Qed.
Lemma lem6936052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936053 {_127128 : Type'} (x : type684 _127128) : (term377 _127128 x) = (term378 _127128 x).
Proof. exact (MK_COMB (@lem6936052) (@lem6936051 _127128 x)). Qed.
Lemma lem6936054 {_127128 : Type'} : (term324 _127128) = (term324 _127128).
Proof. exact (eq_refl (term324 _127128)). Qed.
Lemma lem6936055 {_127128 : Type'} (x : type684 _127128) : (term379 _127128 x) = (term380 _127128 x).
Proof. exact (MK_COMB (@lem6936053 _127128 x) (@lem6936054 _127128)). Qed.
Lemma lem6936056 {_127128 : Type'} : (term381 _127128) = (term382 _127128).
Proof. exact (fun_ext (fun x : type684 _127128 => @lem6936055 _127128 x)). Qed.
Lemma lem6936057 {_127128 : Type'} : (@ex ((_127128 -> Prop) -> _127128)) = (@ex ((_127128 -> Prop) -> _127128)).
Proof. exact (eq_refl (@ex ((_127128 -> Prop) -> _127128))). Qed.
Lemma lem6936058 {_127128 : Type'} : (term370 _127128) = (term383 _127128).
Proof. exact (MK_COMB (@lem6936057 _127128) (@lem6936056 _127128)). Qed.
Lemma lem6936059 {_127128 : Type'} : ((term369 _127128) = (term370 _127128)) = ((term364 _127128) = (term383 _127128)).
Proof. exact (MK_COMB (@lem6936050 _127128) (@lem6936058 _127128)). Qed.
Lemma lem6936060 {_127128 : Type'} : (term364 _127128) = (term383 _127128).
Proof. exact (EQ_MP (@lem6936059 _127128) (@lem6936040 _127128)). Qed.
Lemma lem6936061 {_127128 : Type'} : (term325 _127128) = (term383 _127128).
Proof. exact (TRANS (@lem6936036 _127128) (@lem6936060 _127128)). Qed.
Lemma lem6936062 {_127128 : Type'} : (term301 _127128) = (term383 _127128).
Proof. exact (TRANS (@lem6935870 _127128) (@lem6936061 _127128)). Qed.
Lemma lem6936063 {_127128 : Type'} : (term11 _127128) = (term383 _127128).
Proof. exact (TRANS (@lem6935843 _127128) (@lem6936062 _127128)). Qed.
Lemma lem6936064 {_127128 : Type'} (h1 : term11 _127128) : term383 _127128.
Proof. exact (EQ_MP (@lem6936063 _127128) (@lem6934789 _127128 h1)). Qed.
Lemma lem6936065 {_127128 : Type'} (x : type684 _127128) (h1 : term380 _127128 x) : term380 _127128 x.
Proof. exact (h1). Qed.
Lemma lem6936067 {_127128 : Type'} (x'' : type695 _127128) (h1 : term271 _127128 x'') : term271 _127128 x''.
Proof. exact (h1). Qed.
Lemma lem6936068 {_127128 : Type'} (f : _127128 -> nat) (h1 : term99 _127128 f) : term99 _127128 f.
Proof. exact (h1). Qed.
Lemma lem6936069 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (h1 : term90 _127128 f g) : term90 _127128 f g.
Proof. exact (h1). Qed.
Lemma lem6936070 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term80 _127128 f s g.
Proof. exact (h1). Qed.
Lemma lem6936077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936078 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936077 nat (nat -> Prop) f x). Qed.
Lemma lem6936079 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem6936078 Peano.le m). Qed.
Lemma lem6936080 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6936081 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem6936079 m) (@lem6936080 n)). Qed.
Lemma lem6936083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936084 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936083 nat Prop f x). Qed.
Lemma lem6936085 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term384 m n).
Proof. exact (@lem6936084 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem6936087 (m : nat) (n : nat) : (Peano.le m n) = (term384 m n).
Proof. exact (TRANS (@lem6936081 m n) (@lem6936085 m n)). Qed.
Lemma lem6936088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936095 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936096 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936095 nat (nat -> Prop) f x). Qed.
Lemma lem6936097 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem6936096 Peano.lt m). Qed.
Lemma lem6936098 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6936099 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem6936097 m) (@lem6936098 n)). Qed.
Lemma lem6936101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936102 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936101 nat Prop f x). Qed.
Lemma lem6936103 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term385 m n).
Proof. exact (@lem6936102 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem6936105 (m : nat) (n : nat) : (Peano.lt m n) = (term385 m n).
Proof. exact (TRANS (@lem6936099 m n) (@lem6936103 m n)). Qed.
Lemma lem6936106 (m : nat) (n : nat) : (term386 m n) = (term387 m n).
Proof. exact (MK_COMB (@lem6936088) (@lem6936105 m n)). Qed.
Lemma lem6936107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936108 (m : nat) (n : nat) : (term388 m n) = (term389 m n).
Proof. exact (MK_COMB (@lem6936107) (@lem6936106 m n)). Qed.
Lemma lem6936109 (m : nat) (n : nat) : (term275 m n) = (term390 m n).
Proof. exact (MK_COMB (@lem6936108 m n) (@lem6936087 m n)). Qed.
Lemma lem6936110 (m : nat) : (term276 m) = (term391 m).
Proof. exact (fun_ext (fun n : nat => @lem6936109 m n)). Qed.
Lemma lem6936111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6936112 (m : nat) : (term277 m) = (term392 m).
Proof. exact (MK_COMB (@lem6936111) (@lem6936110 m)). Qed.
Lemma lem6936113 : term278 = term393.
Proof. exact (fun_ext (fun m : nat => @lem6936112 m)). Qed.
Lemma lem6936114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6936115 : term279 = term394.
Proof. exact (MK_COMB (@lem6936114) (@lem6936113)). Qed.
Lemma lem6936116 (h1 : term38) : term394.
Proof. exact (EQ_MP (@lem6936115) (@lem6935810 h1)). Qed.
Lemma lem6936123 {_127128 : Type'} (s : _127128 -> Prop) : (term29 _127128 s) = (term29 _127128 s).
Proof. exact (eq_refl (term29 _127128 s)). Qed.
Lemma lem6936124 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936132 {_127128 : Type'} (f : type1364 _127128) (x : _127128) : (f x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936131 _127128 (type686 _127128) f x). Qed.
Lemma lem6936133 {_127128 : Type'} (x : _127128) : (@IN _127128 x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x).
Proof. exact (@lem6936132 _127128 (@IN _127128) x). Qed.
Lemma lem6936134 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936135 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s).
Proof. exact (MK_COMB (@lem6936133 _127128 x) (@lem6936134 _127128 s)). Qed.
Lemma lem6936137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936138 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936137 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936139 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s) = (term395 _127128 x s).
Proof. exact (@lem6936138 _127128 (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x) s). Qed.
Lemma lem6936141 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (term395 _127128 x s).
Proof. exact (TRANS (@lem6936135 _127128 x s) (@lem6936139 _127128 x s)). Qed.
Lemma lem6936142 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term284 _127128 x s) = (term396 _127128 x s).
Proof. exact (MK_COMB (@lem6936124) (@lem6936141 _127128 x s)). Qed.
Lemma lem6936143 {_127128 : Type'} (s : _127128 -> Prop) : (term286 _127128 s) = (term397 _127128 s).
Proof. exact (fun_ext (fun x : _127128 => @lem6936142 _127128 x s)). Qed.
Lemma lem6936144 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6936145 {_127128 : Type'} (s : _127128 -> Prop) : (term287 _127128 s) = (term398 _127128 s).
Proof. exact (MK_COMB (@lem6936144 _127128) (@lem6936143 _127128 s)). Qed.
Lemma lem6936146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936147 {_127128 : Type'} (s : _127128 -> Prop) : (term290 _127128 s) = (term399 _127128 s).
Proof. exact (MK_COMB (@lem6936146) (@lem6936145 _127128 s)). Qed.
Lemma lem6936148 {_127128 : Type'} (s : _127128 -> Prop) : (term292 _127128 s) = (term400 _127128 s).
Proof. exact (MK_COMB (@lem6936147 _127128 s) (@lem6936123 _127128 s)). Qed.
Lemma lem6936149 {_127128 : Type'} : (term309 _127128) = (term401 _127128).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6936148 _127128 s)). Qed.
Lemma lem6936150 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936151 {_127128 : Type'} : (term324 _127128) = (term402 _127128).
Proof. exact (MK_COMB (@lem6936150 _127128) (@lem6936149 _127128)). Qed.
Lemma lem6936156 {_127128 : Type'} (s : _127128 -> Prop) : (s = (@EMPTY _127128)) = (s = (@EMPTY _127128)).
Proof. exact (eq_refl (s = (@EMPTY _127128))). Qed.
Lemma lem6936157 {_127128 : Type'} : (@IN _127128) = (@IN _127128).
Proof. exact (eq_refl (@IN _127128)). Qed.
Lemma lem6936162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936163 {_127128 : Type'} (f : type684 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936162 (_127128 -> Prop) _127128 f x). Qed.
Lemma lem6936165 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (x s) = (@I ((_127128 -> Prop) -> _127128) x s).
Proof. exact (@lem6936163 _127128 x s). Qed.
Lemma lem6936166 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936167 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term403 _127128 x s) = (term404 _127128 x s).
Proof. exact (MK_COMB (@lem6936157 _127128) (@lem6936165 _127128 x s)). Qed.
Lemma lem6936168 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term405 _127128 x s) = (term406 _127128 x s).
Proof. exact (MK_COMB (@lem6936167 _127128 x s) (@lem6936166 _127128 s)). Qed.
Lemma lem6936170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936171 {_127128 : Type'} (f : type1364 _127128) (x : _127128) : (f x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936170 _127128 (type686 _127128) f x). Qed.
Lemma lem6936172 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term404 _127128 x s) = (term407 _127128 x s).
Proof. exact (@lem6936171 _127128 (@IN _127128) (@I ((_127128 -> Prop) -> _127128) x s)). Qed.
Lemma lem6936173 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936174 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term406 _127128 x s) = (term408 _127128 x s).
Proof. exact (MK_COMB (@lem6936172 _127128 x s) (@lem6936173 _127128 s)). Qed.
Lemma lem6936176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936177 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936176 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936178 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term408 _127128 x s) = (term409 _127128 x s).
Proof. exact (@lem6936177 _127128 (term407 _127128 x s) s). Qed.
Lemma lem6936179 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term406 _127128 x s) = (term409 _127128 x s).
Proof. exact (TRANS (@lem6936174 _127128 x s) (@lem6936178 _127128 x s)). Qed.
Lemma lem6936180 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term405 _127128 x s) = (term409 _127128 x s).
Proof. exact (TRANS (@lem6936168 _127128 x s) (@lem6936179 _127128 x s)). Qed.
Lemma lem6936181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936182 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term410 _127128 x s) = (term411 _127128 x s).
Proof. exact (MK_COMB (@lem6936181) (@lem6936180 _127128 x s)). Qed.
Lemma lem6936183 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term355 _127128 x s) = (term412 _127128 x s).
Proof. exact (MK_COMB (@lem6936182 _127128 x s) (@lem6936156 _127128 s)). Qed.
Lemma lem6936184 {_127128 : Type'} (x : type684 _127128) : (term357 _127128 x) = (term413 _127128 x).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6936183 _127128 x s)). Qed.
Lemma lem6936185 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936186 {_127128 : Type'} (x : type684 _127128) : (term359 _127128 x) = (term414 _127128 x).
Proof. exact (MK_COMB (@lem6936185 _127128) (@lem6936184 _127128 x)). Qed.
Lemma lem6936187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936188 {_127128 : Type'} (x : type684 _127128) : (term378 _127128 x) = (term415 _127128 x).
Proof. exact (MK_COMB (@lem6936187) (@lem6936186 _127128 x)). Qed.
Lemma lem6936189 {_127128 : Type'} (x : type684 _127128) : (term380 _127128 x) = (term416 _127128 x).
Proof. exact (MK_COMB (@lem6936188 _127128 x) (@lem6936151 _127128)). Qed.
Lemma lem6936190 {_127128 : Type'} (x : type684 _127128) (h1 : term380 _127128 x) : term416 _127128 x.
Proof. exact (EQ_MP (@lem6936189 _127128 x) (@lem6936065 _127128 x h1)). Qed.
Lemma lem6936454 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6936461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936462 {_127128 : Type'} (f : type644 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936461 (_127128 -> Prop) (type705 _127128) f x). Qed.
Lemma lem6936463 {_127128 : Type'} (s : _127128 -> Prop) : (@nsum _127128 s) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s).
Proof. exact (@lem6936462 _127128 (@nsum _127128) s). Qed.
Lemma lem6936464 {_127128 : Type'} (f : _127128 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6936465 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@nsum _127128 s f) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s f).
Proof. exact (MK_COMB (@lem6936463 _127128 s) (@lem6936464 _127128 f)). Qed.
Lemma lem6936467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936468 {_127128 : Type'} (f : type705 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936467 (_127128 -> nat) nat f x). Qed.
Lemma lem6936469 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s f) = (term417 _127128 s f).
Proof. exact (@lem6936468 _127128 (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s) f). Qed.
Lemma lem6936471 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@nsum _127128 s f) = (term417 _127128 s f).
Proof. exact (TRANS (@lem6936465 _127128 s f) (@lem6936469 _127128 s f)). Qed.
Lemma lem6936478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936479 {_127128 : Type'} (f : type644 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936478 (_127128 -> Prop) (type705 _127128) f x). Qed.
Lemma lem6936480 {_127128 : Type'} (s : _127128 -> Prop) : (@nsum _127128 s) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s).
Proof. exact (@lem6936479 _127128 (@nsum _127128) s). Qed.
Lemma lem6936481 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936482 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@nsum _127128 s g) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s g).
Proof. exact (MK_COMB (@lem6936480 _127128 s) (@lem6936481 _127128 g)). Qed.
Lemma lem6936484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936485 {_127128 : Type'} (f : type705 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936484 (_127128 -> nat) nat f x). Qed.
Lemma lem6936486 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s g) = (term417 _127128 s g).
Proof. exact (@lem6936485 _127128 (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s) g). Qed.
Lemma lem6936488 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@nsum _127128 s g) = (term417 _127128 s g).
Proof. exact (TRANS (@lem6936482 _127128 s g) (@lem6936486 _127128 s g)). Qed.
Lemma lem6936489 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (term418 _127128 s f) = (term419 _127128 s f).
Proof. exact (MK_COMB (@lem6936454) (@lem6936471 _127128 s f)). Qed.
Lemma lem6936490 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term420 _127128 f s g).
Proof. exact (MK_COMB (@lem6936489 _127128 s f) (@lem6936488 _127128 s g)). Qed.
Lemma lem6936492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936493 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936492 nat (nat -> Prop) f x). Qed.
Lemma lem6936494 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (term419 _127128 s f) = (term421 _127128 s f).
Proof. exact (@lem6936493 Peano.lt (term417 _127128 s f)). Qed.
Lemma lem6936495 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (term417 _127128 s g) = (term417 _127128 s g).
Proof. exact (eq_refl (term417 _127128 s g)). Qed.
Lemma lem6936496 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term420 _127128 f s g) = (term422 _127128 f s g).
Proof. exact (MK_COMB (@lem6936494 _127128 s f) (@lem6936495 _127128 s g)). Qed.
Lemma lem6936498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936499 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936498 nat Prop f x). Qed.
Lemma lem6936500 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term422 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (@lem6936499 (term421 _127128 s f) (term417 _127128 s g)). Qed.
Lemma lem6936501 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term420 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (TRANS (@lem6936496 _127128 f s g) (@lem6936500 _127128 f s g)). Qed.
Lemma lem6936502 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (TRANS (@lem6936490 _127128 f s g) (@lem6936501 _127128 f s g)). Qed.
Lemma lem6936503 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936504 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6936509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936511 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936509 _127128 nat f x). Qed.
Lemma lem6936516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936517 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936516 _127128 nat f x). Qed.
Lemma lem6936519 {_127128 : Type'} (g : _127128 -> nat) (x : _127128) : (g x) = (@I (_127128 -> nat) g x).
Proof. exact (@lem6936517 _127128 g x). Qed.
Lemma lem6936520 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (term424 _127128 f x) = (term425 _127128 f x).
Proof. exact (MK_COMB (@lem6936504) (@lem6936511 _127128 f x)). Qed.
Lemma lem6936521 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term71 _127128 f g x) = (term426 _127128 f g x).
Proof. exact (MK_COMB (@lem6936520 _127128 f x) (@lem6936519 _127128 g x)). Qed.
Lemma lem6936523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936524 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936523 nat (nat -> Prop) f x). Qed.
Lemma lem6936525 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (term425 _127128 f x) = (term427 _127128 f x).
Proof. exact (@lem6936524 Peano.lt (@I (_127128 -> nat) f x)). Qed.
Lemma lem6936526 {_127128 : Type'} (g : _127128 -> nat) (x : _127128) : (@I (_127128 -> nat) g x) = (@I (_127128 -> nat) g x).
Proof. exact (eq_refl (@I (_127128 -> nat) g x)). Qed.
Lemma lem6936527 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term426 _127128 f g x) = (term428 _127128 f g x).
Proof. exact (MK_COMB (@lem6936525 _127128 f x) (@lem6936526 _127128 g x)). Qed.
Lemma lem6936529 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936530 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936529 nat Prop f x). Qed.
Lemma lem6936531 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term428 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (@lem6936530 (term427 _127128 f x) (@I (_127128 -> nat) g x)). Qed.
Lemma lem6936532 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term426 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (TRANS (@lem6936527 _127128 f g x) (@lem6936531 _127128 f g x)). Qed.
Lemma lem6936533 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term71 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (TRANS (@lem6936521 _127128 f g x) (@lem6936532 _127128 f g x)). Qed.
Lemma lem6936534 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term430 _127128 f g x) = (term431 _127128 f g x).
Proof. exact (MK_COMB (@lem6936503) (@lem6936533 _127128 f g x)). Qed.
Lemma lem6936535 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936543 {_127128 : Type'} (f : type1364 _127128) (x : _127128) : (f x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936542 _127128 (type686 _127128) f x). Qed.
Lemma lem6936544 {_127128 : Type'} (x : _127128) : (@IN _127128 x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x).
Proof. exact (@lem6936543 _127128 (@IN _127128) x). Qed.
Lemma lem6936545 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936546 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s).
Proof. exact (MK_COMB (@lem6936544 _127128 x) (@lem6936545 _127128 s)). Qed.
Lemma lem6936548 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936549 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936548 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936550 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s) = (term395 _127128 x s).
Proof. exact (@lem6936549 _127128 (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x) s). Qed.
Lemma lem6936552 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (term395 _127128 x s).
Proof. exact (TRANS (@lem6936546 _127128 x s) (@lem6936550 _127128 x s)). Qed.
Lemma lem6936553 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term284 _127128 x s) = (term396 _127128 x s).
Proof. exact (MK_COMB (@lem6936535) (@lem6936552 _127128 x s)). Qed.
Lemma lem6936554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936555 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term432 _127128 x s) = (term433 _127128 x s).
Proof. exact (MK_COMB (@lem6936554) (@lem6936553 _127128 x s)). Qed.
Lemma lem6936556 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term119 _127128 s f g x) = (term434 _127128 s f g x).
Proof. exact (MK_COMB (@lem6936555 _127128 x s) (@lem6936534 _127128 f g x)). Qed.
Lemma lem6936557 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term127 _127128 s f g) = (term435 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6936556 _127128 s f g x)). Qed.
Lemma lem6936558 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6936559 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term128 _127128 s f g) = (term436 _127128 s f g).
Proof. exact (MK_COMB (@lem6936558 _127128) (@lem6936557 _127128 s f g)). Qed.
Lemma lem6936560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936561 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6936562 {_127128 : Type'} (f : _127128 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6936571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936572 {_127128 : Type'} (f : type695 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936571 (_127128 -> nat) (type694 _127128) f x). Qed.
Lemma lem6936573 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (x'' f) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f).
Proof. exact (@lem6936572 _127128 x'' f). Qed.
Lemma lem6936574 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936575 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g).
Proof. exact (MK_COMB (@lem6936573 _127128 x'' f) (@lem6936574 _127128 g)). Qed.
Lemma lem6936577 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936578 {_127128 : Type'} (f : type694 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936577 (_127128 -> nat) (type684 _127128) f x). Qed.
Lemma lem6936579 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g) = (term437 _127128 x'' f g).
Proof. exact (@lem6936578 _127128 (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f) g). Qed.
Lemma lem6936580 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (term437 _127128 x'' f g).
Proof. exact (TRANS (@lem6936575 _127128 x'' f g) (@lem6936579 _127128 x'' f g)). Qed.
Lemma lem6936581 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936582 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term438 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936580 _127128 x'' f g) (@lem6936581 _127128 s)). Qed.
Lemma lem6936584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936585 {_127128 : Type'} (f : type684 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936584 (_127128 -> Prop) _127128 f x). Qed.
Lemma lem6936586 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term438 _127128 x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (@lem6936585 _127128 (term437 _127128 x'' f g) s). Qed.
Lemma lem6936588 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936582 _127128 x'' f g s) (@lem6936586 _127128 x'' f g s)). Qed.
Lemma lem6936589 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term440 _127128 x'' f g s) = (term441 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936562 _127128 f) (@lem6936588 _127128 x'' f g s)). Qed.
Lemma lem6936591 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936592 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936591 _127128 nat f x). Qed.
Lemma lem6936593 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term441 _127128 x'' f g s) = (term442 _127128 x'' f g s).
Proof. exact (@lem6936592 _127128 f (term439 _127128 x'' f g s)). Qed.
Lemma lem6936594 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term440 _127128 x'' f g s) = (term442 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936589 _127128 x'' f g s) (@lem6936593 _127128 x'' f g s)). Qed.
Lemma lem6936595 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936604 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936605 {_127128 : Type'} (f : type695 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936604 (_127128 -> nat) (type694 _127128) f x). Qed.
Lemma lem6936606 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (x'' f) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f).
Proof. exact (@lem6936605 _127128 x'' f). Qed.
Lemma lem6936607 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936608 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g).
Proof. exact (MK_COMB (@lem6936606 _127128 x'' f) (@lem6936607 _127128 g)). Qed.
Lemma lem6936610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936611 {_127128 : Type'} (f : type694 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936610 (_127128 -> nat) (type684 _127128) f x). Qed.
Lemma lem6936612 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g) = (term437 _127128 x'' f g).
Proof. exact (@lem6936611 _127128 (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f) g). Qed.
Lemma lem6936613 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (term437 _127128 x'' f g).
Proof. exact (TRANS (@lem6936608 _127128 x'' f g) (@lem6936612 _127128 x'' f g)). Qed.
Lemma lem6936614 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936615 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term438 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936613 _127128 x'' f g) (@lem6936614 _127128 s)). Qed.
Lemma lem6936617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936618 {_127128 : Type'} (f : type684 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936617 (_127128 -> Prop) _127128 f x). Qed.
Lemma lem6936619 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term438 _127128 x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (@lem6936618 _127128 (term437 _127128 x'' f g) s). Qed.
Lemma lem6936621 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936615 _127128 x'' f g s) (@lem6936619 _127128 x'' f g s)). Qed.
Lemma lem6936622 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term443 _127128 x'' f g s) = (term444 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936595 _127128 g) (@lem6936621 _127128 x'' f g s)). Qed.
Lemma lem6936624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936625 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936624 _127128 nat f x). Qed.
Lemma lem6936626 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term444 _127128 x'' f g s) = (term445 _127128 x'' f g s).
Proof. exact (@lem6936625 _127128 g (term439 _127128 x'' f g s)). Qed.
Lemma lem6936627 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term443 _127128 x'' f g s) = (term445 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936622 _127128 x'' f g s) (@lem6936626 _127128 x'' f g s)). Qed.
Lemma lem6936628 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term446 _127128 x'' f g s) = (term447 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936561) (@lem6936594 _127128 x'' f g s)). Qed.
Lemma lem6936629 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term448 _127128 x'' f g s) = (term449 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936628 _127128 x'' f g s) (@lem6936627 _127128 x'' f g s)). Qed.
Lemma lem6936631 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936632 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936631 nat (nat -> Prop) f x). Qed.
Lemma lem6936633 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term447 _127128 x'' f g s) = (term450 _127128 x'' f g s).
Proof. exact (@lem6936632 Peano.le (term442 _127128 x'' f g s)). Qed.
Lemma lem6936634 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term445 _127128 x'' f g s) = (term445 _127128 x'' f g s).
Proof. exact (eq_refl (term445 _127128 x'' f g s)). Qed.
Lemma lem6936635 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term449 _127128 x'' f g s) = (term451 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936633 _127128 x'' f g s) (@lem6936634 _127128 x'' f g s)). Qed.
Lemma lem6936637 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936638 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936637 nat Prop f x). Qed.
Lemma lem6936639 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term451 _127128 x'' f g s) = (term452 _127128 x'' f g s).
Proof. exact (@lem6936638 (term450 _127128 x'' f g s) (term445 _127128 x'' f g s)). Qed.
Lemma lem6936640 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term449 _127128 x'' f g s) = (term452 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936635 _127128 x'' f g s) (@lem6936639 _127128 x'' f g s)). Qed.
Lemma lem6936641 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term448 _127128 x'' f g s) = (term452 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936629 _127128 x'' f g s) (@lem6936640 _127128 x'' f g s)). Qed.
Lemma lem6936642 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term453 _127128 x'' f g s) = (term454 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936560) (@lem6936641 _127128 x'' f g s)). Qed.
Lemma lem6936643 {_127128 : Type'} : (@IN _127128) = (@IN _127128).
Proof. exact (eq_refl (@IN _127128)). Qed.
Lemma lem6936652 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936653 {_127128 : Type'} (f : type695 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936652 (_127128 -> nat) (type694 _127128) f x). Qed.
Lemma lem6936654 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (x'' f) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f).
Proof. exact (@lem6936653 _127128 x'' f). Qed.
Lemma lem6936655 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936656 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g).
Proof. exact (MK_COMB (@lem6936654 _127128 x'' f) (@lem6936655 _127128 g)). Qed.
Lemma lem6936658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936659 {_127128 : Type'} (f : type694 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> (_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936658 (_127128 -> nat) (type684 _127128) f x). Qed.
Lemma lem6936660 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f g) = (term437 _127128 x'' f g).
Proof. exact (@lem6936659 _127128 (@I ((_127128 -> nat) -> (_127128 -> nat) -> (_127128 -> Prop) -> _127128) x'' f) g). Qed.
Lemma lem6936661 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (x'' f g) = (term437 _127128 x'' f g).
Proof. exact (TRANS (@lem6936656 _127128 x'' f g) (@lem6936660 _127128 x'' f g)). Qed.
Lemma lem6936662 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936663 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term438 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936661 _127128 x'' f g) (@lem6936662 _127128 s)). Qed.
Lemma lem6936665 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936666 {_127128 : Type'} (f : type684 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> _127128) f x).
Proof. exact (@lem6936665 (_127128 -> Prop) _127128 f x). Qed.
Lemma lem6936667 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term438 _127128 x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (@lem6936666 _127128 (term437 _127128 x'' f g) s). Qed.
Lemma lem6936669 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (x'' f g s) = (term439 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936663 _127128 x'' f g s) (@lem6936667 _127128 x'' f g s)). Qed.
Lemma lem6936670 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936671 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term455 _127128 x'' f g s) = (term456 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936643 _127128) (@lem6936669 _127128 x'' f g s)). Qed.
Lemma lem6936672 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term457 _127128 x'' f g s) = (term458 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936671 _127128 x'' f g s) (@lem6936670 _127128 s)). Qed.
Lemma lem6936674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936675 {_127128 : Type'} (f : type1364 _127128) (x : _127128) : (f x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936674 _127128 (type686 _127128) f x). Qed.
Lemma lem6936676 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term456 _127128 x'' f g s) = (term459 _127128 x'' f g s).
Proof. exact (@lem6936675 _127128 (@IN _127128) (term439 _127128 x'' f g s)). Qed.
Lemma lem6936677 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936678 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term458 _127128 x'' f g s) = (term460 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936676 _127128 x'' f g s) (@lem6936677 _127128 s)). Qed.
Lemma lem6936680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936681 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936680 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936682 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term460 _127128 x'' f g s) = (term461 _127128 x'' f g s).
Proof. exact (@lem6936681 _127128 (term459 _127128 x'' f g s) s). Qed.
Lemma lem6936683 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term458 _127128 x'' f g s) = (term461 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936678 _127128 x'' f g s) (@lem6936682 _127128 x'' f g s)). Qed.
Lemma lem6936684 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term457 _127128 x'' f g s) = (term461 _127128 x'' f g s).
Proof. exact (TRANS (@lem6936672 _127128 x'' f g s) (@lem6936683 _127128 x'' f g s)). Qed.
Lemma lem6936685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936686 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term462 _127128 x'' f g s) = (term463 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936685) (@lem6936684 _127128 x'' f g s)). Qed.
Lemma lem6936687 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term464 _127128 x'' f g s) = (term465 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936686 _127128 x'' f g s) (@lem6936642 _127128 x'' f g s)). Qed.
Lemma lem6936688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936689 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term466 _127128 x'' f g s) = (term467 _127128 x'' f g s).
Proof. exact (MK_COMB (@lem6936688) (@lem6936687 _127128 x'' f g s)). Qed.
Lemma lem6936690 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term468 _127128 x'' s f g) = (term469 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6936689 _127128 x'' f g s) (@lem6936559 _127128 s f g)). Qed.
Lemma lem6936691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936697 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936696 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936699 {_127128 : Type'} (s : _127128 -> Prop) : (@FINITE _127128 s) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s).
Proof. exact (@lem6936697 _127128 (@FINITE _127128) s). Qed.
Lemma lem6936700 {_127128 : Type'} (s : _127128 -> Prop) : (term170 _127128 s) = (term470 _127128 s).
Proof. exact (MK_COMB (@lem6936691) (@lem6936699 _127128 s)). Qed.
Lemma lem6936701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936702 {_127128 : Type'} (s : _127128 -> Prop) : (term134 _127128 s) = (term471 _127128 s).
Proof. exact (MK_COMB (@lem6936701) (@lem6936700 _127128 s)). Qed.
Lemma lem6936703 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term472 _127128 x'' s f g) = (term473 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6936702 _127128 s) (@lem6936690 _127128 x'' s f g)). Qed.
Lemma lem6936704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936705 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term474 _127128 x'' s f g) = (term475 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6936704) (@lem6936703 _127128 x'' s f g)). Qed.
Lemma lem6936706 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term476 _127128 x'' f s g) = (term477 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6936705 _127128 x'' s f g) (@lem6936502 _127128 f s g)). Qed.
Lemma lem6936707 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term478 _127128 x'' f g) = (term479 _127128 x'' f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6936706 _127128 x'' f s g)). Qed.
Lemma lem6936708 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6936709 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term480 _127128 x'' f g) = (term481 _127128 x'' f g).
Proof. exact (MK_COMB (@lem6936708 _127128) (@lem6936707 _127128 x'' f g)). Qed.
Lemma lem6936710 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term482 _127128 x'' f) = (term483 _127128 x'' f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6936709 _127128 x'' f g)). Qed.
Lemma lem6936711 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6936712 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term267 _127128 x'' f) = (term484 _127128 x'' f).
Proof. exact (MK_COMB (@lem6936711 _127128) (@lem6936710 _127128 x'' f)). Qed.
Lemma lem6936713 {_127128 : Type'} (x'' : type695 _127128) : (term269 _127128 x'') = (term485 _127128 x'').
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6936712 _127128 x'' f)). Qed.
Lemma lem6936714 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6936715 {_127128 : Type'} (x'' : type695 _127128) : (term271 _127128 x'') = (term486 _127128 x'').
Proof. exact (MK_COMB (@lem6936714 _127128) (@lem6936713 _127128 x'')). Qed.
Lemma lem6936716 {_127128 : Type'} (x'' : type695 _127128) (h1 : term271 _127128 x'') : term486 _127128 x''.
Proof. exact (EQ_MP (@lem6936715 _127128 x'') (@lem6936067 _127128 x'' h1)). Qed.
Lemma lem6936717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936718 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6936725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936726 {_127128 : Type'} (f : type644 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936725 (_127128 -> Prop) (type705 _127128) f x). Qed.
Lemma lem6936727 {_127128 : Type'} (s : _127128 -> Prop) : (@nsum _127128 s) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s).
Proof. exact (@lem6936726 _127128 (@nsum _127128) s). Qed.
Lemma lem6936728 {_127128 : Type'} (f : _127128 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6936729 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@nsum _127128 s f) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s f).
Proof. exact (MK_COMB (@lem6936727 _127128 s) (@lem6936728 _127128 f)). Qed.
Lemma lem6936731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936732 {_127128 : Type'} (f : type705 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936731 (_127128 -> nat) nat f x). Qed.
Lemma lem6936733 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s f) = (term417 _127128 s f).
Proof. exact (@lem6936732 _127128 (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s) f). Qed.
Lemma lem6936735 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (@nsum _127128 s f) = (term417 _127128 s f).
Proof. exact (TRANS (@lem6936729 _127128 s f) (@lem6936733 _127128 s f)). Qed.
Lemma lem6936742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936743 {_127128 : Type'} (f : type644 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936742 (_127128 -> Prop) (type705 _127128) f x). Qed.
Lemma lem6936744 {_127128 : Type'} (s : _127128 -> Prop) : (@nsum _127128 s) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s).
Proof. exact (@lem6936743 _127128 (@nsum _127128) s). Qed.
Lemma lem6936745 {_127128 : Type'} (g : _127128 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6936746 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@nsum _127128 s g) = (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s g).
Proof. exact (MK_COMB (@lem6936744 _127128 s) (@lem6936745 _127128 g)). Qed.
Lemma lem6936748 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936749 {_127128 : Type'} (f : type705 _127128) (x : _127128 -> nat) : (f x) = (@I ((_127128 -> nat) -> nat) f x).
Proof. exact (@lem6936748 (_127128 -> nat) nat f x). Qed.
Lemma lem6936750 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s g) = (term417 _127128 s g).
Proof. exact (@lem6936749 _127128 (@I ((_127128 -> Prop) -> (_127128 -> nat) -> nat) (@nsum _127128) s) g). Qed.
Lemma lem6936752 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (@nsum _127128 s g) = (term417 _127128 s g).
Proof. exact (TRANS (@lem6936746 _127128 s g) (@lem6936750 _127128 s g)). Qed.
Lemma lem6936753 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (term418 _127128 s f) = (term419 _127128 s f).
Proof. exact (MK_COMB (@lem6936718) (@lem6936735 _127128 s f)). Qed.
Lemma lem6936754 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term420 _127128 f s g).
Proof. exact (MK_COMB (@lem6936753 _127128 s f) (@lem6936752 _127128 s g)). Qed.
Lemma lem6936756 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936757 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936756 nat (nat -> Prop) f x). Qed.
Lemma lem6936758 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) : (term419 _127128 s f) = (term421 _127128 s f).
Proof. exact (@lem6936757 Peano.lt (term417 _127128 s f)). Qed.
Lemma lem6936759 {_127128 : Type'} (s : _127128 -> Prop) (g : _127128 -> nat) : (term417 _127128 s g) = (term417 _127128 s g).
Proof. exact (eq_refl (term417 _127128 s g)). Qed.
Lemma lem6936760 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term420 _127128 f s g) = (term422 _127128 f s g).
Proof. exact (MK_COMB (@lem6936758 _127128 s f) (@lem6936759 _127128 s g)). Qed.
Lemma lem6936762 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936763 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936762 nat Prop f x). Qed.
Lemma lem6936764 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term422 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (@lem6936763 (term421 _127128 s f) (term417 _127128 s g)). Qed.
Lemma lem6936765 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term420 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (TRANS (@lem6936760 _127128 f s g) (@lem6936764 _127128 f s g)). Qed.
Lemma lem6936766 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term39 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (TRANS (@lem6936754 _127128 f s g) (@lem6936765 _127128 f s g)). Qed.
Lemma lem6936767 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term76 _127128 f s g) = (term487 _127128 f s g).
Proof. exact (MK_COMB (@lem6936717) (@lem6936766 _127128 f s g)). Qed.
Lemma lem6936768 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6936773 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936775 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936773 _127128 nat f x). Qed.
Lemma lem6936780 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936781 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (f x) = (@I (_127128 -> nat) f x).
Proof. exact (@lem6936780 _127128 nat f x). Qed.
Lemma lem6936783 {_127128 : Type'} (g : _127128 -> nat) (x : _127128) : (g x) = (@I (_127128 -> nat) g x).
Proof. exact (@lem6936781 _127128 g x). Qed.
Lemma lem6936784 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (term424 _127128 f x) = (term425 _127128 f x).
Proof. exact (MK_COMB (@lem6936768) (@lem6936775 _127128 f x)). Qed.
Lemma lem6936785 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term71 _127128 f g x) = (term426 _127128 f g x).
Proof. exact (MK_COMB (@lem6936784 _127128 f x) (@lem6936783 _127128 g x)). Qed.
Lemma lem6936787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936788 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6936787 nat (nat -> Prop) f x). Qed.
Lemma lem6936789 {_127128 : Type'} (f : _127128 -> nat) (x : _127128) : (term425 _127128 f x) = (term427 _127128 f x).
Proof. exact (@lem6936788 Peano.lt (@I (_127128 -> nat) f x)). Qed.
Lemma lem6936790 {_127128 : Type'} (g : _127128 -> nat) (x : _127128) : (@I (_127128 -> nat) g x) = (@I (_127128 -> nat) g x).
Proof. exact (eq_refl (@I (_127128 -> nat) g x)). Qed.
Lemma lem6936791 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term426 _127128 f g x) = (term428 _127128 f g x).
Proof. exact (MK_COMB (@lem6936789 _127128 f x) (@lem6936790 _127128 g x)). Qed.
Lemma lem6936793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936794 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6936793 nat Prop f x). Qed.
Lemma lem6936795 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term428 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (@lem6936794 (term427 _127128 f x) (@I (_127128 -> nat) g x)). Qed.
Lemma lem6936796 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term426 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (TRANS (@lem6936791 _127128 f g x) (@lem6936795 _127128 f g x)). Qed.
Lemma lem6936797 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term71 _127128 f g x) = (term429 _127128 f g x).
Proof. exact (TRANS (@lem6936785 _127128 f g x) (@lem6936796 _127128 f g x)). Qed.
Lemma lem6936798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6936805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936806 {_127128 : Type'} (f : type1364 _127128) (x : _127128) : (f x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936805 _127128 (type686 _127128) f x). Qed.
Lemma lem6936807 {_127128 : Type'} (x : _127128) : (@IN _127128 x) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x).
Proof. exact (@lem6936806 _127128 (@IN _127128) x). Qed.
Lemma lem6936808 {_127128 : Type'} (s : _127128 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6936809 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s).
Proof. exact (MK_COMB (@lem6936807 _127128 x) (@lem6936808 _127128 s)). Qed.
Lemma lem6936811 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936812 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936811 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936813 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x s) = (term395 _127128 x s).
Proof. exact (@lem6936812 _127128 (@I (_127128 -> (_127128 -> Prop) -> Prop) (@IN _127128) x) s). Qed.
Lemma lem6936815 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (@IN _127128 x s) = (term395 _127128 x s).
Proof. exact (TRANS (@lem6936809 _127128 x s) (@lem6936813 _127128 x s)). Qed.
Lemma lem6936816 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term284 _127128 x s) = (term396 _127128 x s).
Proof. exact (MK_COMB (@lem6936798) (@lem6936815 _127128 x s)). Qed.
Lemma lem6936817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6936818 {_127128 : Type'} (x : _127128) (s : _127128 -> Prop) : (term432 _127128 x s) = (term433 _127128 x s).
Proof. exact (MK_COMB (@lem6936817) (@lem6936816 _127128 x s)). Qed.
Lemma lem6936819 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term70 _127128 s f g x) = (term488 _127128 s f g x).
Proof. exact (MK_COMB (@lem6936818 _127128 x s) (@lem6936797 _127128 f g x)). Qed.
Lemma lem6936820 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term72 _127128 s f g) = (term489 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6936819 _127128 s f g x)). Qed.
Lemma lem6936821 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6936822 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term73 _127128 s f g) = (term490 _127128 s f g).
Proof. exact (MK_COMB (@lem6936821 _127128) (@lem6936820 _127128 s f g)). Qed.
Lemma lem6936831 {_127128 : Type'} (s : _127128 -> Prop) : (term60 _127128 s) = (term60 _127128 s).
Proof. exact (eq_refl (term60 _127128 s)). Qed.
Lemma lem6936832 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term74 _127128 s f g) = (term491 _127128 s f g).
Proof. exact (MK_COMB (@lem6936831 _127128 s) (@lem6936822 _127128 s f g)). Qed.
Lemma lem6936837 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6936838 {_127128 : Type'} (f : type686 _127128) (x : _127128 -> Prop) : (f x) = (@I ((_127128 -> Prop) -> Prop) f x).
Proof. exact (@lem6936837 (_127128 -> Prop) Prop f x). Qed.
Lemma lem6936840 {_127128 : Type'} (s : _127128 -> Prop) : (@FINITE _127128 s) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s).
Proof. exact (@lem6936838 _127128 (@FINITE _127128) s). Qed.
Lemma lem6936841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936842 {_127128 : Type'} (s : _127128 -> Prop) : (term48 _127128 s) = (term492 _127128 s).
Proof. exact (MK_COMB (@lem6936841) (@lem6936840 _127128 s)). Qed.
Lemma lem6936843 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term75 _127128 s f g) = (term493 _127128 s f g).
Proof. exact (MK_COMB (@lem6936842 _127128 s) (@lem6936832 _127128 s f g)). Qed.
Lemma lem6936844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6936845 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term78 _127128 s f g) = (term494 _127128 s f g).
Proof. exact (MK_COMB (@lem6936844) (@lem6936843 _127128 s f g)). Qed.
Lemma lem6936846 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term80 _127128 f s g) = (term495 _127128 f s g).
Proof. exact (MK_COMB (@lem6936845 _127128 s f g) (@lem6936767 _127128 f s g)). Qed.
Lemma lem6936847 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term495 _127128 f s g.
Proof. exact (EQ_MP (@lem6936846 _127128 f s g) (@lem6936070 _127128 f s g h1)). Qed.
Lemma lem6936849 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term493 _127128 s f g.
Proof. exact (proj1 (@lem6936847 _127128 f s g h1)). Qed.
Lemma lem6936850 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term491 _127128 s f g.
Proof. exact (proj2 (@lem6936849 _127128 f s g h1)). Qed.
Lemma lem6936852 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term490 _127128 s f g.
Proof. exact (proj2 (@lem6936850 _127128 f s g h1)). Qed.
Lemma lem6936855 {_127128 : Type'} (x : type684 _127128) (h1 : term380 _127128 x) : term414 _127128 x.
Proof. exact (proj1 (@lem6936190 _127128 x h1)). Qed.
Lemma lem6936863 (m : nat) (n : nat) : (term390 m n) = (term390 m n).
Proof. exact (eq_refl (term390 m n)). Qed.
Lemma lem6936864 (m : nat) : (term391 m) = (term391 m).
Proof. exact (fun_ext (fun n : nat => @lem6936863 m n)). Qed.
Lemma lem6936865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6936866 (m : nat) : (term392 m) = (term392 m).
Proof. exact (MK_COMB (@lem6936865) (@lem6936864 m)). Qed.
Lemma lem6936867 : term393 = term393.
Proof. exact (fun_ext (fun m : nat => @lem6936866 m)). Qed.
Lemma lem6936868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6936870 : term394 = term394.
Proof. exact (MK_COMB (@lem6936868) (@lem6936867)). Qed.
Lemma lem6936871 (h1 : term38) : term394.
Proof. exact (EQ_MP (@lem6936870) (@lem6936116 h1)). Qed.
Lemma lem6937015 {A : Type'} (P : Prop) (Q : A -> Prop) : (term496 A P Q) = (term497 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6937016 {_127128 : Type'} (P : Prop) (Q : _127128 -> Prop) : (term496 _127128 P Q) = (term497 _127128 P Q).
Proof. exact (@lem6937015 _127128 P Q). Qed.
Lemma lem6937017 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term498 _127128 x'' s f g) = (term499 _127128 x'' s f g).
Proof. exact (@lem6937016 _127128 (term465 _127128 x'' f g s) (term435 _127128 s f g)). Qed.
Lemma lem6937018 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term500 _127128 s f g x) = (term434 _127128 s f g x).
Proof. exact (eq_refl (term500 _127128 s f g x)). Qed.
Lemma lem6937019 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term501 _127128 s f g) = (term435 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937018 _127128 s f g x)). Qed.
Lemma lem6937020 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937021 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term502 _127128 s f g) = (term436 _127128 s f g).
Proof. exact (MK_COMB (@lem6937020 _127128) (@lem6937019 _127128 s f g)). Qed.
Lemma lem6937022 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term467 _127128 x'' f g s) = (term467 _127128 x'' f g s).
Proof. exact (eq_refl (term467 _127128 x'' f g s)). Qed.
Lemma lem6937023 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term498 _127128 x'' s f g) = (term469 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937022 _127128 x'' f g s) (@lem6937021 _127128 s f g)). Qed.
Lemma lem6937024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6937025 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term503 _127128 x'' s f g) = (term504 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937024) (@lem6937023 _127128 x'' s f g)). Qed.
Lemma lem6937026 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term500 _127128 s f g x) = (term434 _127128 s f g x).
Proof. exact (eq_refl (term500 _127128 s f g x)). Qed.
Lemma lem6937027 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term467 _127128 x'' f g s) = (term467 _127128 x'' f g s).
Proof. exact (eq_refl (term467 _127128 x'' f g s)). Qed.
Lemma lem6937028 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term505 _127128 x'' s f g x) = (term506 _127128 x'' s f g x).
Proof. exact (MK_COMB (@lem6937027 _127128 x'' f g s) (@lem6937026 _127128 s f g x)). Qed.
Lemma lem6937029 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term507 _127128 x'' s f g) = (term508 _127128 x'' s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937028 _127128 x'' s f g x)). Qed.
Lemma lem6937030 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937031 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term499 _127128 x'' s f g) = (term509 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937030 _127128) (@lem6937029 _127128 x'' s f g)). Qed.
Lemma lem6937032 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : ((term498 _127128 x'' s f g) = (term499 _127128 x'' s f g)) = ((term469 _127128 x'' s f g) = (term509 _127128 x'' s f g)).
Proof. exact (MK_COMB (@lem6937025 _127128 x'' s f g) (@lem6937031 _127128 x'' s f g)). Qed.
Lemma lem6937033 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term469 _127128 x'' s f g) = (term509 _127128 x'' s f g).
Proof. exact (EQ_MP (@lem6937032 _127128 x'' s f g) (@lem6937017 _127128 x'' s f g)). Qed.
Lemma lem6937034 {_127128 : Type'} (s : _127128 -> Prop) : (term471 _127128 s) = (term471 _127128 s).
Proof. exact (eq_refl (term471 _127128 s)). Qed.
Lemma lem6937035 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term473 _127128 x'' s f g) = (term510 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937034 _127128 s) (@lem6937033 _127128 x'' s f g)). Qed.
Lemma lem6937037 {A : Type'} (P : Prop) (Q : A -> Prop) : (term496 A P Q) = (term497 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6937038 {_127128 : Type'} (P : Prop) (Q : _127128 -> Prop) : (term496 _127128 P Q) = (term497 _127128 P Q).
Proof. exact (@lem6937037 _127128 P Q). Qed.
Lemma lem6937039 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term511 _127128 x'' s f g) = (term512 _127128 x'' s f g).
Proof. exact (@lem6937038 _127128 (term470 _127128 s) (term508 _127128 x'' s f g)). Qed.
Lemma lem6937040 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term513 _127128 x'' s f g x) = (term506 _127128 x'' s f g x).
Proof. exact (eq_refl (term513 _127128 x'' s f g x)). Qed.
Lemma lem6937041 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term514 _127128 x'' s f g) = (term508 _127128 x'' s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937040 _127128 x'' s f g x)). Qed.
Lemma lem6937042 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937043 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term515 _127128 x'' s f g) = (term509 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937042 _127128) (@lem6937041 _127128 x'' s f g)). Qed.
Lemma lem6937044 {_127128 : Type'} (s : _127128 -> Prop) : (term471 _127128 s) = (term471 _127128 s).
Proof. exact (eq_refl (term471 _127128 s)). Qed.
Lemma lem6937045 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term511 _127128 x'' s f g) = (term510 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937044 _127128 s) (@lem6937043 _127128 x'' s f g)). Qed.
Lemma lem6937046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6937047 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term516 _127128 x'' s f g) = (term517 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937046) (@lem6937045 _127128 x'' s f g)). Qed.
Lemma lem6937048 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term513 _127128 x'' s f g x) = (term506 _127128 x'' s f g x).
Proof. exact (eq_refl (term513 _127128 x'' s f g x)). Qed.
Lemma lem6937049 {_127128 : Type'} (s : _127128 -> Prop) : (term471 _127128 s) = (term471 _127128 s).
Proof. exact (eq_refl (term471 _127128 s)). Qed.
Lemma lem6937050 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term518 _127128 x'' s f g x) = (term519 _127128 x'' s f g x).
Proof. exact (MK_COMB (@lem6937049 _127128 s) (@lem6937048 _127128 x'' s f g x)). Qed.
Lemma lem6937051 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term520 _127128 x'' s f g) = (term521 _127128 x'' s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937050 _127128 x'' s f g x)). Qed.
Lemma lem6937052 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937053 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term512 _127128 x'' s f g) = (term522 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937052 _127128) (@lem6937051 _127128 x'' s f g)). Qed.
Lemma lem6937054 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : ((term511 _127128 x'' s f g) = (term512 _127128 x'' s f g)) = ((term510 _127128 x'' s f g) = (term522 _127128 x'' s f g)).
Proof. exact (MK_COMB (@lem6937047 _127128 x'' s f g) (@lem6937053 _127128 x'' s f g)). Qed.
Lemma lem6937055 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term510 _127128 x'' s f g) = (term522 _127128 x'' s f g).
Proof. exact (EQ_MP (@lem6937054 _127128 x'' s f g) (@lem6937039 _127128 x'' s f g)). Qed.
Lemma lem6937056 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term473 _127128 x'' s f g) = (term522 _127128 x'' s f g).
Proof. exact (TRANS (@lem6937035 _127128 x'' s f g) (@lem6937055 _127128 x'' s f g)). Qed.
Lemma lem6937057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6937058 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term475 _127128 x'' s f g) = (term523 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937057) (@lem6937056 _127128 x'' s f g)). Qed.
Lemma lem6937059 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term423 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (eq_refl (term423 _127128 f s g)). Qed.
Lemma lem6937060 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term477 _127128 x'' f s g) = (term524 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6937058 _127128 x'' s f g) (@lem6937059 _127128 f s g)). Qed.
Lemma lem6937062 {A : Type'} (P : A -> Prop) (Q : Prop) : (term525 A P Q) = (term526 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6937063 {_127128 : Type'} (P : _127128 -> Prop) (Q : Prop) : (term525 _127128 P Q) = (term526 _127128 P Q).
Proof. exact (@lem6937062 _127128 P Q). Qed.
Lemma lem6937064 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term527 _127128 x'' f s g) = (term528 _127128 x'' f s g).
Proof. exact (@lem6937063 _127128 (term521 _127128 x'' s f g) (term423 _127128 f s g)). Qed.
Lemma lem6937065 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term529 _127128 x'' s f g x) = (term519 _127128 x'' s f g x).
Proof. exact (eq_refl (term529 _127128 x'' s f g x)). Qed.
Lemma lem6937066 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term530 _127128 x'' s f g) = (term521 _127128 x'' s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937065 _127128 x'' s f g x)). Qed.
Lemma lem6937067 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937068 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term531 _127128 x'' s f g) = (term522 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937067 _127128) (@lem6937066 _127128 x'' s f g)). Qed.
Lemma lem6937069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6937070 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term532 _127128 x'' s f g) = (term523 _127128 x'' s f g).
Proof. exact (MK_COMB (@lem6937069) (@lem6937068 _127128 x'' s f g)). Qed.
Lemma lem6937071 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term423 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (eq_refl (term423 _127128 f s g)). Qed.
Lemma lem6937072 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term527 _127128 x'' f s g) = (term524 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6937070 _127128 x'' s f g) (@lem6937071 _127128 f s g)). Qed.
Lemma lem6937073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6937074 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term533 _127128 x'' f s g) = (term534 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6937073) (@lem6937072 _127128 x'' f s g)). Qed.
Lemma lem6937075 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term529 _127128 x'' s f g x) = (term519 _127128 x'' s f g x).
Proof. exact (eq_refl (term529 _127128 x'' s f g x)). Qed.
Lemma lem6937076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6937077 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term535 _127128 x'' s f g x) = (term536 _127128 x'' s f g x).
Proof. exact (MK_COMB (@lem6937076) (@lem6937075 _127128 x'' s f g x)). Qed.
Lemma lem6937078 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term423 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (eq_refl (term423 _127128 f s g)). Qed.
Lemma lem6937079 {_127128 : Type'} (x'' : type695 _127128) (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term537 _127128 x'' x f s g) = (term538 _127128 x'' x f s g).
Proof. exact (MK_COMB (@lem6937077 _127128 x'' s f g x) (@lem6937078 _127128 f s g)). Qed.
Lemma lem6937080 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term539 _127128 x'' f s g) = (term540 _127128 x'' f s g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937079 _127128 x'' x f s g)). Qed.
Lemma lem6937081 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937082 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term528 _127128 x'' f s g) = (term541 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6937081 _127128) (@lem6937080 _127128 x'' f s g)). Qed.
Lemma lem6937083 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : ((term527 _127128 x'' f s g) = (term528 _127128 x'' f s g)) = ((term524 _127128 x'' f s g) = (term541 _127128 x'' f s g)).
Proof. exact (MK_COMB (@lem6937074 _127128 x'' f s g) (@lem6937082 _127128 x'' f s g)). Qed.
Lemma lem6937084 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term524 _127128 x'' f s g) = (term541 _127128 x'' f s g).
Proof. exact (EQ_MP (@lem6937083 _127128 x'' f s g) (@lem6937064 _127128 x'' f s g)). Qed.
Lemma lem6937085 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term477 _127128 x'' f s g) = (term541 _127128 x'' f s g).
Proof. exact (TRANS (@lem6937060 _127128 x'' f s g) (@lem6937084 _127128 x'' f s g)). Qed.
Lemma lem6937086 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term479 _127128 x'' f g) = (term542 _127128 x'' f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6937085 _127128 x'' f s g)). Qed.
Lemma lem6937087 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6937088 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term481 _127128 x'' f g) = (term543 _127128 x'' f g).
Proof. exact (MK_COMB (@lem6937087 _127128) (@lem6937086 _127128 x'' f g)). Qed.
Lemma lem6937089 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term483 _127128 x'' f) = (term544 _127128 x'' f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6937088 _127128 x'' f g)). Qed.
Lemma lem6937090 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6937091 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term484 _127128 x'' f) = (term545 _127128 x'' f).
Proof. exact (MK_COMB (@lem6937090 _127128) (@lem6937089 _127128 x'' f)). Qed.
Lemma lem6937092 {_127128 : Type'} (x'' : type695 _127128) : (term485 _127128 x'') = (term546 _127128 x'').
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6937091 _127128 x'' f)). Qed.
Lemma lem6937093 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6937094 {_127128 : Type'} (x'' : type695 _127128) : (term486 _127128 x'') = (term547 _127128 x'').
Proof. exact (MK_COMB (@lem6937093 _127128) (@lem6937092 _127128 x'')). Qed.
Lemma lem6937095 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term423 _127128 f s g) = (term423 _127128 f s g).
Proof. exact (eq_refl (term423 _127128 f s g)). Qed.
Lemma lem6937118 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term506 _127128 x'' s f g x) = (term548 _127128 x'' s f g x).
Proof. exact (@lem19699 (term461 _127128 x'' f g s) (term454 _127128 x'' f g s) (term434 _127128 s f g x)). Qed.
Lemma lem6937121 {_127128 : Type'} (s : _127128 -> Prop) : (term471 _127128 s) = (term471 _127128 s).
Proof. exact (eq_refl (term471 _127128 s)). Qed.
Lemma lem6937122 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term519 _127128 x'' s f g x) = (term549 _127128 x'' s f g x).
Proof. exact (MK_COMB (@lem6937121 _127128 s) (@lem6937118 _127128 x'' s f g x)). Qed.
Lemma lem6937129 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term549 _127128 x'' s f g x) = (term550 _127128 x'' s f g x).
Proof. exact (@lem19490 (term551 _127128 x'' s f g x) (term470 _127128 s) (term552 _127128 x'' s f g x)). Qed.
Lemma lem6937130 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term519 _127128 x'' s f g x) = (term550 _127128 x'' s f g x).
Proof. exact (TRANS (@lem6937122 _127128 x'' s f g x) (@lem6937129 _127128 x'' s f g x)). Qed.
Lemma lem6937131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6937132 {_127128 : Type'} (x'' : type695 _127128) (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term536 _127128 x'' s f g x) = (term553 _127128 x'' s f g x).
Proof. exact (MK_COMB (@lem6937131) (@lem6937130 _127128 x'' s f g x)). Qed.
Lemma lem6937133 {_127128 : Type'} (x'' : type695 _127128) (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term538 _127128 x'' x f s g) = (term554 _127128 x'' x f s g).
Proof. exact (MK_COMB (@lem6937132 _127128 x'' s f g x) (@lem6937095 _127128 f s g)). Qed.
Lemma lem6937140 {_127128 : Type'} (x'' : type695 _127128) (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term554 _127128 x'' x f s g) = (term555 _127128 x'' x f s g).
Proof. exact (@lem19699 (term556 _127128 x'' s f g x) (term557 _127128 x'' s f g x) (term423 _127128 f s g)). Qed.
Lemma lem6937141 {_127128 : Type'} (x'' : type695 _127128) (x : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term538 _127128 x'' x f s g) = (term555 _127128 x'' x f s g).
Proof. exact (TRANS (@lem6937133 _127128 x'' x f s g) (@lem6937140 _127128 x'' x f s g)). Qed.
Lemma lem6937142 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term540 _127128 x'' f s g) = (term558 _127128 x'' f s g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937141 _127128 x'' x f s g)). Qed.
Lemma lem6937143 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937144 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term541 _127128 x'' f s g) = (term559 _127128 x'' f s g).
Proof. exact (MK_COMB (@lem6937143 _127128) (@lem6937142 _127128 x'' f s g)). Qed.
Lemma lem6937145 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term542 _127128 x'' f g) = (term560 _127128 x'' f g).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6937144 _127128 x'' f s g)). Qed.
Lemma lem6937146 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6937147 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) : (term543 _127128 x'' f g) = (term561 _127128 x'' f g).
Proof. exact (MK_COMB (@lem6937146 _127128) (@lem6937145 _127128 x'' f g)). Qed.
Lemma lem6937148 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term544 _127128 x'' f) = (term562 _127128 x'' f).
Proof. exact (fun_ext (fun g : _127128 -> nat => @lem6937147 _127128 x'' f g)). Qed.
Lemma lem6937149 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6937150 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) : (term545 _127128 x'' f) = (term563 _127128 x'' f).
Proof. exact (MK_COMB (@lem6937149 _127128) (@lem6937148 _127128 x'' f)). Qed.
Lemma lem6937151 {_127128 : Type'} (x'' : type695 _127128) : (term546 _127128 x'') = (term564 _127128 x'').
Proof. exact (fun_ext (fun f : _127128 -> nat => @lem6937150 _127128 x'' f)). Qed.
Lemma lem6937152 {_127128 : Type'} : (@all (_127128 -> nat)) = (@all (_127128 -> nat)).
Proof. exact (eq_refl (@all (_127128 -> nat))). Qed.
Lemma lem6937153 {_127128 : Type'} (x'' : type695 _127128) : (term547 _127128 x'') = (term565 _127128 x'').
Proof. exact (MK_COMB (@lem6937152 _127128) (@lem6937151 _127128 x'')). Qed.
Lemma lem6937154 {_127128 : Type'} (x'' : type695 _127128) : (term486 _127128 x'') = (term565 _127128 x'').
Proof. exact (TRANS (@lem6937094 _127128 x'') (@lem6937153 _127128 x'')). Qed.
Lemma lem6937155 {_127128 : Type'} (x'' : type695 _127128) (h1 : term271 _127128 x'') : term565 _127128 x''.
Proof. exact (EQ_MP (@lem6937154 _127128 x'') (@lem6936716 _127128 x'' h1)). Qed.
Lemma lem6937175 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (x : _127128) : (term488 _127128 s f g x) = (term488 _127128 s f g x).
Proof. exact (eq_refl (term488 _127128 s f g x)). Qed.
Lemma lem6937176 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term489 _127128 s f g) = (term489 _127128 s f g).
Proof. exact (fun_ext (fun x : _127128 => @lem6937175 _127128 s f g x)). Qed.
Lemma lem6937177 {_127128 : Type'} : (@all _127128) = (@all _127128).
Proof. exact (eq_refl (@all _127128)). Qed.
Lemma lem6937179 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) : (term490 _127128 s f g) = (term490 _127128 s f g).
Proof. exact (MK_COMB (@lem6937177 _127128) (@lem6937176 _127128 s f g)). Qed.
Lemma lem6937180 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term490 _127128 s f g.
Proof. exact (EQ_MP (@lem6937179 _127128 s f g) (@lem6936852 _127128 f s g h1)). Qed.
Lemma lem6937188 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term412 _127128 x s) = (term412 _127128 x s).
Proof. exact (eq_refl (term412 _127128 x s)). Qed.
Lemma lem6937189 {_127128 : Type'} (x : type684 _127128) : (term413 _127128 x) = (term413 _127128 x).
Proof. exact (fun_ext (fun s : _127128 -> Prop => @lem6937188 _127128 x s)). Qed.
Lemma lem6937190 {_127128 : Type'} : (@all (_127128 -> Prop)) = (@all (_127128 -> Prop)).
Proof. exact (eq_refl (@all (_127128 -> Prop))). Qed.
Lemma lem6937192 {_127128 : Type'} (x : type684 _127128) : (term414 _127128 x) = (term414 _127128 x).
Proof. exact (MK_COMB (@lem6937190 _127128) (@lem6937189 _127128 x)). Qed.
Lemma lem6937193 {_127128 : Type'} (x : type684 _127128) (h1 : term380 _127128 x) : term414 _127128 x.
Proof. exact (EQ_MP (@lem6937192 _127128 x) (@lem6936855 _127128 x h1)). Qed.
Lemma lem6937236 (_92441 : nat) (h1 : term38) : term566 _92441.
Proof. exact (@lem6936871 h1 _92441). Qed.
Lemma lem6937237 (_92441 : nat) : (term566 _92441) = (term392 _92441).
Proof. exact (eq_refl (term566 _92441)). Qed.
Lemma lem6937238 (_92441 : nat) (h1 : term38) : term392 _92441.
Proof. exact (EQ_MP (@lem6937237 _92441) (@lem6937236 _92441 h1)). Qed.
Lemma lem6937239 (_92441 : nat) (_92442 : nat) (h1 : term38) : term567 _92441 _92442.
Proof. exact (@lem6937238 _92441 h1 _92442). Qed.
Lemma lem6937240 (_92441 : nat) (_92442 : nat) : (term567 _92441 _92442) = (term390 _92441 _92442).
Proof. exact (eq_refl (term567 _92441 _92442)). Qed.
Lemma lem6937254 {_127128 : Type'} (_92447 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term568 _127128 x'' _92447.
Proof. exact (@lem6937155 _127128 x'' h1 _92447). Qed.
Lemma lem6937255 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) : (term568 _127128 x'' _92447) = (term563 _127128 x'' _92447).
Proof. exact (eq_refl (term568 _127128 x'' _92447)). Qed.
Lemma lem6937256 {_127128 : Type'} (_92447 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term563 _127128 x'' _92447.
Proof. exact (EQ_MP (@lem6937255 _127128 x'' _92447) (@lem6937254 _127128 _92447 x'' h1)). Qed.
Lemma lem6937257 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term569 _127128 x'' _92447 _92448.
Proof. exact (@lem6937256 _127128 _92447 x'' h1 _92448). Qed.
Lemma lem6937258 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) : (term569 _127128 x'' _92447 _92448) = (term561 _127128 x'' _92447 _92448).
Proof. exact (eq_refl (term569 _127128 x'' _92447 _92448)). Qed.
Lemma lem6937259 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term561 _127128 x'' _92447 _92448.
Proof. exact (EQ_MP (@lem6937258 _127128 x'' _92447 _92448) (@lem6937257 _127128 _92447 _92448 x'' h1)). Qed.
Lemma lem6937260 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term570 _127128 x'' _92447 _92448 _92449.
Proof. exact (@lem6937259 _127128 _92447 _92448 x'' h1 _92449). Qed.
Lemma lem6937261 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term570 _127128 x'' _92447 _92448 _92449) = (term559 _127128 x'' _92447 _92449 _92448).
Proof. exact (eq_refl (term570 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6937262 {_127128 : Type'} (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term559 _127128 x'' _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6937261 _127128 x'' _92447 _92449 _92448) (@lem6937260 _127128 _92447 _92448 _92449 x'' h1)). Qed.
Lemma lem6937263 {_127128 : Type'} (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (_92450 : _127128) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term571 _127128 x'' _92447 _92449 _92448 _92450.
Proof. exact (@lem6937262 _127128 _92447 _92449 _92448 x'' h1 _92450). Qed.
Lemma lem6937264 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term571 _127128 x'' _92447 _92449 _92448 _92450) = (term555 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (eq_refl (term571 _127128 x'' _92447 _92449 _92448 _92450)). Qed.
Lemma lem6937265 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term555 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6937264 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937263 _127128 _92447 _92449 _92448 _92450 x'' h1)). Qed.
Lemma lem6937266 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term572 _127128 s f g _92451.
Proof. exact (@lem6937180 _127128 f s g h1 _92451). Qed.
Lemma lem6937267 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) : (term572 _127128 s f g _92451) = (term488 _127128 s f g _92451).
Proof. exact (eq_refl (term572 _127128 s f g _92451)). Qed.
Lemma lem6937269 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term573 _127128 x _92452.
Proof. exact (@lem6937193 _127128 x h1 _92452). Qed.
Lemma lem6937270 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term573 _127128 x _92452) = (term412 _127128 x _92452).
Proof. exact (eq_refl (term573 _127128 x _92452)). Qed.
Lemma lem6937278 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term574 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (proj2 (@lem6937265 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6937279 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term575 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (proj1 (@lem6937265 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6937287 (_92441 : nat) (_92442 : nat) (h1 : term38) : term390 _92441 _92442.
Proof. exact (EQ_MP (@lem6937240 _92441 _92442) (@lem6937239 _92441 _92442 h1)). Qed.
Lemma lem6937293 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term29 _127128 s.
Proof. exact (proj1 (@lem6936850 _127128 f s g h1)). Qed.
Lemma lem6937299 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term488 _127128 s f g _92451.
Proof. exact (EQ_MP (@lem6937267 _127128 s f g _92451) (@lem6937266 _127128 _92451 f s g h1)). Qed.
Lemma lem6937305 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term412 _127128 x _92452.
Proof. exact (EQ_MP (@lem6937270 _127128 x _92452) (@lem6937269 _127128 _92452 x h1)). Qed.
Lemma lem6937315 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term575 _127128 x'' _92450 _92447 _92449 _92448) = (term576 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term470 _127128 _92449) (term551 _127128 x'' _92449 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937316 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term577 _127128 x'' _92450 _92447 _92449 _92448) = (term578 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term461 _127128 x'' _92447 _92448 _92449) (term434 _127128 _92449 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937323 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term579 _127128 _92450 _92447 _92449 _92448) = (term580 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term396 _127128 _92450 _92449) (term431 _127128 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937324 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term581 _127128 x'' _92447 _92448 _92449) = (term581 _127128 x'' _92447 _92448 _92449).
Proof. exact (eq_refl (term581 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6937327 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term578 _127128 x'' _92450 _92447 _92449 _92448) = (term582 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6937324 _127128 x'' _92447 _92448 _92449) (@lem6937323 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937328 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term577 _127128 x'' _92450 _92447 _92449 _92448) = (term582 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6937316 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937327 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937329 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6937332 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term576 _127128 x'' _92450 _92447 _92449 _92448) = (term583 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6937329 _127128 _92449) (@lem6937328 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937334 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term575 _127128 x'' _92450 _92447 _92449 _92448) = (term583 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6937315 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937332 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937335 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term583 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6937334 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937279 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6937339 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term574 _127128 x'' _92450 _92447 _92449 _92448) = (term584 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term470 _127128 _92449) (term552 _127128 x'' _92449 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937340 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term585 _127128 x'' _92450 _92447 _92449 _92448) = (term586 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term454 _127128 x'' _92447 _92448 _92449) (term434 _127128 _92449 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937347 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term579 _127128 _92450 _92447 _92449 _92448) = (term580 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6934243 (term396 _127128 _92450 _92449) (term431 _127128 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6937348 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term587 _127128 x'' _92447 _92448 _92449) = (term587 _127128 x'' _92447 _92448 _92449).
Proof. exact (eq_refl (term587 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6937351 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term586 _127128 x'' _92450 _92447 _92449 _92448) = (term588 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6937348 _127128 x'' _92447 _92448 _92449) (@lem6937347 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937352 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term585 _127128 x'' _92450 _92447 _92449 _92448) = (term588 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6937340 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937351 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937353 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6937356 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term584 _127128 x'' _92450 _92447 _92449 _92448) = (term589 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6937353 _127128 _92449) (@lem6937352 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937358 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term574 _127128 x'' _92450 _92447 _92449 _92448) = (term589 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6937339 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937356 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937359 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term589 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6937358 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937278 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6937737 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : @I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s.
Proof. exact (proj1 (@lem6936849 _127128 f s g h1)). Qed.
Lemma lem6937738 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term590 _127128 s.
Proof. exact (fun h0 : term470 _127128 s => @lem6937737 _127128 f s g h1). Qed.
Lemma lem6937740 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6937741 {_127128 : Type'} (s : _127128 -> Prop) : (term590 _127128 s) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s).
Proof. exact (@lem6937740 (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s)). Qed.
Lemma lem6937742 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : @I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s.
Proof. exact (EQ_MP (@lem6937741 _127128 s) (@lem6937738 _127128 f s g h1)). Qed.
Lemma lem6937744 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : @I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s.
Proof. exact (proj1 (@lem6936849 _127128 f s g h1)). Qed.
Lemma lem6937745 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term590 _127128 s.
Proof. exact (fun h0 : term470 _127128 s => @lem6937744 _127128 f s g h1). Qed.
Lemma lem6937747 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6937748 {_127128 : Type'} (s : _127128 -> Prop) : (term590 _127128 s) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s).
Proof. exact (@lem6937747 (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s)). Qed.
Lemma lem6937749 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : @I ((_127128 -> Prop) -> Prop) (@FINITE _127128) s.
Proof. exact (EQ_MP (@lem6937748 _127128 s) (@lem6937745 _127128 f s g h1)). Qed.
Lemma lem6937752 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (h1). Qed.
Lemma lem6937753 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term592 _127128 s.
Proof. exact (fun h0 : s = (@EMPTY _127128) => @lem6937752 _127128 s h1). Qed.
Lemma lem6937755 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6937756 {_127128 : Type'} (s : _127128 -> Prop) : (term592 _127128 s) = (term29 _127128 s).
Proof. exact (@lem6937755 (s = (@EMPTY _127128))). Qed.
Lemma lem6937757 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (EQ_MP (@lem6937756 _127128 s) (@lem6937753 _127128 s h1)). Qed.
Lemma lem6937759 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6937762 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term412 _127128 x _92452) = (term595 _127128 x _92452).
Proof. exact (@lem6937759 (_92452 = (@EMPTY _127128)) (term409 _127128 x _92452)). Qed.
Lemma lem6937765 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (EQ_MP (@lem6937762 _127128 x _92452) (@lem6937305 _127128 _92452 x h1)). Qed.
Lemma lem6937766 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (@lem6937765 _127128 _92452 x h1). Qed.
Lemma lem6937767 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x s.
Proof. exact (@lem6937766 _127128 s x h1). Qed.
Lemma lem6937770 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (@lem6937767 _127128 s x h2 (@lem6937757 _127128 s h1)). Qed.
Lemma lem6937771 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term596 _127128 x s.
Proof. exact (fun h0 : term597 _127128 x s => @lem6937770 _127128 s x h1 h2). Qed.
Lemma lem6937773 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6937774 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term596 _127128 x s) = (term409 _127128 x s).
Proof. exact (@lem6937773 (term409 _127128 x s)). Qed.
Lemma lem6937775 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (EQ_MP (@lem6937774 _127128 x s) (@lem6937771 _127128 s x h1 h2)). Qed.
Lemma lem6937778 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (h1). Qed.
Lemma lem6937779 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term592 _127128 s.
Proof. exact (fun h0 : s = (@EMPTY _127128) => @lem6937778 _127128 s h1). Qed.
Lemma lem6937781 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6937782 {_127128 : Type'} (s : _127128 -> Prop) : (term592 _127128 s) = (term29 _127128 s).
Proof. exact (@lem6937781 (s = (@EMPTY _127128))). Qed.
Lemma lem6937783 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (EQ_MP (@lem6937782 _127128 s) (@lem6937779 _127128 s h1)). Qed.
Lemma lem6937785 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (EQ_MP (@lem6937762 _127128 x _92452) (@lem6937305 _127128 _92452 x h1)). Qed.
Lemma lem6937786 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (@lem6937785 _127128 _92452 x h1). Qed.
Lemma lem6937787 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x s.
Proof. exact (@lem6937786 _127128 s x h1). Qed.
Lemma lem6937790 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (@lem6937787 _127128 s x h2 (@lem6937783 _127128 s h1)). Qed.
Lemma lem6937791 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term596 _127128 x s.
Proof. exact (fun h0 : term597 _127128 x s => @lem6937790 _127128 s x h1 h2). Qed.
Lemma lem6937793 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6937794 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term596 _127128 x s) = (term409 _127128 x s).
Proof. exact (@lem6937793 (term409 _127128 x s)). Qed.
Lemma lem6937795 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (EQ_MP (@lem6937794 _127128 x s) (@lem6937791 _127128 s x h1 h2)). Qed.
Lemma lem6937801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6937802 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : (term488 _127128 s f g _92451) = (term598 _127128 f g _92451 s).
Proof. exact (@lem6937801 (term429 _127128 f g _92451) (term396 _127128 _92451 s)). Qed.
Lemma lem6937808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6937809 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : (term599 _127128 s f g _92451) = (term600 _127128 f g _92451 s).
Proof. exact (MK_COMB (@lem6937808) (@lem6937802 _127128 f g _92451 s)). Qed.
Lemma lem6937815 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : (term598 _127128 f g _92451 s) = (term598 _127128 f g _92451 s).
Proof. exact (eq_refl (term598 _127128 f g _92451 s)). Qed.
Lemma lem6937816 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : ((term488 _127128 s f g _92451) = (term598 _127128 f g _92451 s)) = ((term598 _127128 f g _92451 s) = (term598 _127128 f g _92451 s)).
Proof. exact (MK_COMB (@lem6937809 _127128 f g _92451 s) (@lem6937815 _127128 f g _92451 s)). Qed.
Lemma lem6937818 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6937819 (x : Prop) : (x = x) = True.
Proof. exact (@lem6937818 Prop x). Qed.
Lemma lem6937820 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : ((term598 _127128 f g _92451 s) = (term598 _127128 f g _92451 s)) = True.
Proof. exact (@lem6937819 (term598 _127128 f g _92451 s)). Qed.
Lemma lem6937821 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : ((term488 _127128 s f g _92451) = (term598 _127128 f g _92451 s)) = True.
Proof. exact (TRANS (@lem6937816 _127128 f g _92451 s) (@lem6937820 _127128 f g _92451 s)). Qed.
Lemma lem6937822 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : True = ((term488 _127128 s f g _92451) = (term598 _127128 f g _92451 s)).
Proof. exact (SYM (@lem6937821 _127128 f g _92451 s)). Qed.
Lemma lem6937823 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : (term488 _127128 s f g _92451) = (term598 _127128 f g _92451 s).
Proof. exact (EQ_MP (@lem6937822 _127128 f g _92451 s) (@lem0)). Qed.
Lemma lem6937824 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term598 _127128 f g _92451 s.
Proof. exact (EQ_MP (@lem6937823 _127128 f g _92451 s) (@lem6937299 _127128 _92451 f s g h1)). Qed.
Lemma lem6937826 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6937827 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) : (term598 _127128 f g _92451 s) = (term601 _127128 s f g _92451).
Proof. exact (@lem6937826 (term396 _127128 _92451 s) (term429 _127128 f g _92451)). Qed.
Lemma lem6937829 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6937830 {_127128 : Type'} (_92451 : _127128) (s : _127128 -> Prop) : (term603 _127128 _92451 s) = (term395 _127128 _92451 s).
Proof. exact (@lem6937829 (term395 _127128 _92451 s)). Qed.
Lemma lem6937831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6937832 {_127128 : Type'} (_92451 : _127128) (s : _127128 -> Prop) : (term604 _127128 _92451 s) = (term605 _127128 _92451 s).
Proof. exact (MK_COMB (@lem6937831) (@lem6937830 _127128 _92451 s)). Qed.
Lemma lem6937833 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) : (term429 _127128 f g _92451) = (term429 _127128 f g _92451).
Proof. exact (eq_refl (term429 _127128 f g _92451)). Qed.
Lemma lem6937834 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) : (term601 _127128 s f g _92451) = (term606 _127128 s f g _92451).
Proof. exact (MK_COMB (@lem6937832 _127128 _92451 s) (@lem6937833 _127128 f g _92451)). Qed.
Lemma lem6937835 {_127128 : Type'} (s : _127128 -> Prop) (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) : (term598 _127128 f g _92451 s) = (term606 _127128 s f g _92451).
Proof. exact (TRANS (@lem6937827 _127128 s f g _92451) (@lem6937834 _127128 s f g _92451)). Qed.
Lemma lem6937838 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term606 _127128 s f g _92451.
Proof. exact (EQ_MP (@lem6937835 _127128 s f g _92451) (@lem6937824 _127128 _92451 f s g h1)). Qed.
Lemma lem6937839 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term606 _127128 s f g _92451.
Proof. exact (@lem6937838 _127128 _92451 f s g h1). Qed.
Lemma lem6937840 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term607 _127128 f g x s.
Proof. exact (@lem6937839 _127128 (@I ((_127128 -> Prop) -> _127128) x s) f s g h1). Qed.
Lemma lem6937843 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term608 _127128 f g x s.
Proof. exact (@lem6937840 _127128 x f s g h3 (@lem6937795 _127128 s x h1 h2)). Qed.
Lemma lem6937844 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term609 _127128 f g x s.
Proof. exact (fun h0 : term610 _127128 f g x s => @lem6937843 _127128 x f s g h1 h2 h3). Qed.
Lemma lem6937846 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6937847 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) (s : _127128 -> Prop) : (term609 _127128 f g x s) = (term608 _127128 f g x s).
Proof. exact (@lem6937846 (term608 _127128 f g x s)). Qed.
Lemma lem6937848 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term608 _127128 f g x s.
Proof. exact (EQ_MP (@lem6937847 _127128 f g x s) (@lem6937844 _127128 x f s g h1 h2 h3)). Qed.
Lemma lem6937850 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term487 _127128 f s g.
Proof. exact (proj2 (@lem6936847 _127128 f s g h1)). Qed.
Lemma lem6937851 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term611 _127128 f s g.
Proof. exact (fun h0 : term423 _127128 f s g => @lem6937850 _127128 f s g h1). Qed.
Lemma lem6937853 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6937854 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term611 _127128 f s g) = (term487 _127128 f s g).
Proof. exact (@lem6937853 (term423 _127128 f s g)). Qed.
Lemma lem6937855 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term487 _127128 f s g.
Proof. exact (EQ_MP (@lem6937854 _127128 f s g) (@lem6937851 _127128 f s g h1)). Qed.
Lemma lem6937861 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6937862 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term583 _127128 x'' _92450 _92447 _92449 _92448) = (term612 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6937861 (term461 _127128 x'' _92447 _92448 _92449) (term470 _127128 _92449) (term580 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6937896 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6937897 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term613 _127128 _92450 _92447 _92449 _92448) = (term614 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6937896 (term423 _127128 _92447 _92449 _92448) (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6937903 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term433 _127128 _92450 _92449) = (term433 _127128 _92450 _92449).
Proof. exact (eq_refl (term433 _127128 _92450 _92449)). Qed.
Lemma lem6937904 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term580 _127128 _92450 _92447 _92449 _92448) = (term615 _127128 _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6937903 _127128 _92450 _92449) (@lem6937897 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937908 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6937909 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term615 _127128 _92449 _92447 _92448 _92450) = (term616 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6937908 (term423 _127128 _92447 _92449 _92448) (term396 _127128 _92450 _92449) (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6937925 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term580 _127128 _92450 _92447 _92449 _92448) = (term616 _127128 _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6937904 _127128 _92449 _92447 _92448 _92450) (@lem6937909 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937926 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6937927 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term617 _127128 _92450 _92447 _92449 _92448) = (term618 _127128 _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6937926 _127128 _92449) (@lem6937925 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937931 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6937932 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term618 _127128 _92449 _92447 _92448 _92450) = (term619 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6937931 (term423 _127128 _92447 _92449 _92448) (term470 _127128 _92449) (term434 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937958 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term617 _127128 _92450 _92447 _92449 _92448) = (term619 _127128 _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6937927 _127128 _92449 _92447 _92448 _92450) (@lem6937932 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937959 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term581 _127128 x'' _92447 _92448 _92449) = (term581 _127128 x'' _92447 _92448 _92449).
Proof. exact (eq_refl (term581 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6937960 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term612 _127128 x'' _92450 _92447 _92449 _92448) = (term620 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6937959 _127128 x'' _92447 _92448 _92449) (@lem6937958 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937971 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term583 _127128 x'' _92450 _92447 _92449 _92448) = (term620 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6937862 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937960 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6937972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6937973 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term621 _127128 x'' _92450 _92447 _92449 _92448) = (term622 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6937972) (@lem6937971 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938007 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6938008 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term613 _127128 _92450 _92447 _92449 _92448) = (term614 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6938007 (term423 _127128 _92447 _92449 _92448) (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938014 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term433 _127128 _92450 _92449) = (term433 _127128 _92450 _92449).
Proof. exact (eq_refl (term433 _127128 _92450 _92449)). Qed.
Lemma lem6938015 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term580 _127128 _92450 _92447 _92449 _92448) = (term615 _127128 _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6938014 _127128 _92450 _92449) (@lem6938008 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938019 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938020 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term615 _127128 _92449 _92447 _92448 _92450) = (term616 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6938019 (term423 _127128 _92447 _92449 _92448) (term396 _127128 _92450 _92449) (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938036 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term580 _127128 _92450 _92447 _92449 _92448) = (term616 _127128 _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6938015 _127128 _92449 _92447 _92448 _92450) (@lem6938020 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938037 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6938038 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term617 _127128 _92450 _92447 _92449 _92448) = (term618 _127128 _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6938037 _127128 _92449) (@lem6938036 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938042 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938043 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term618 _127128 _92449 _92447 _92448 _92450) = (term619 _127128 _92449 _92447 _92448 _92450).
Proof. exact (@lem6938042 (term423 _127128 _92447 _92449 _92448) (term470 _127128 _92449) (term434 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938069 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term617 _127128 _92450 _92447 _92449 _92448) = (term619 _127128 _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6938038 _127128 _92449 _92447 _92448 _92450) (@lem6938043 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938070 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term581 _127128 x'' _92447 _92448 _92449) = (term581 _127128 x'' _92447 _92448 _92449).
Proof. exact (eq_refl (term581 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938071 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term612 _127128 x'' _92450 _92447 _92449 _92448) = (term620 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6938070 _127128 x'' _92447 _92448 _92449) (@lem6938069 _127128 _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938082 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : ((term583 _127128 x'' _92450 _92447 _92449 _92448) = (term612 _127128 x'' _92450 _92447 _92449 _92448)) = ((term620 _127128 x'' _92449 _92447 _92448 _92450) = (term620 _127128 x'' _92449 _92447 _92448 _92450)).
Proof. exact (MK_COMB (@lem6937973 _127128 x'' _92449 _92447 _92448 _92450) (@lem6938071 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938084 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6938085 (x : Prop) : (x = x) = True.
Proof. exact (@lem6938084 Prop x). Qed.
Lemma lem6938086 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : ((term620 _127128 x'' _92449 _92447 _92448 _92450) = (term620 _127128 x'' _92449 _92447 _92448 _92450)) = True.
Proof. exact (@lem6938085 (term620 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938087 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : ((term583 _127128 x'' _92450 _92447 _92449 _92448) = (term612 _127128 x'' _92450 _92447 _92449 _92448)) = True.
Proof. exact (TRANS (@lem6938082 _127128 x'' _92449 _92447 _92448 _92450) (@lem6938086 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938088 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : True = ((term583 _127128 x'' _92450 _92447 _92449 _92448) = (term612 _127128 x'' _92450 _92447 _92449 _92448)).
Proof. exact (SYM (@lem6938087 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938089 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term583 _127128 x'' _92450 _92447 _92449 _92448) = (term612 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (EQ_MP (@lem6938088 _127128 x'' _92450 _92447 _92449 _92448) (@lem0)). Qed.
Lemma lem6938090 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term612 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6938089 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937335 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6938092 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6938093 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term612 _127128 x'' _92450 _92447 _92449 _92448) = (term623 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938092 (term617 _127128 _92450 _92447 _92449 _92448) (term461 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938095 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938096 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term626 _127128 _92450 _92447 _92449 _92448) = (term627 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6938095 (term470 _127128 _92449) (term580 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938098 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938099 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term628 _127128 _92449) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) _92449).
Proof. exact (@lem6938098 (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) _92449)). Qed.
Lemma lem6938100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938101 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term629 _127128 _92449) = (term492 _127128 _92449).
Proof. exact (MK_COMB (@lem6938100) (@lem6938099 _127128 _92449)). Qed.
Lemma lem6938103 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938104 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term630 _127128 _92450 _92447 _92449 _92448) = (term631 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6938103 (term396 _127128 _92450 _92449) (term613 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938106 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938107 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term603 _127128 _92450 _92449) = (term395 _127128 _92450 _92449).
Proof. exact (@lem6938106 (term395 _127128 _92450 _92449)). Qed.
Lemma lem6938108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938109 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term632 _127128 _92450 _92449) = (term633 _127128 _92450 _92449).
Proof. exact (MK_COMB (@lem6938108) (@lem6938107 _127128 _92450 _92449)). Qed.
Lemma lem6938111 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938112 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term634 _127128 _92450 _92447 _92449 _92448) = (term635 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6938111 (term431 _127128 _92447 _92448 _92450) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938114 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938115 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term636 _127128 _92447 _92448 _92450) = (term429 _127128 _92447 _92448 _92450).
Proof. exact (@lem6938114 (term429 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938117 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term637 _127128 _92447 _92448 _92450) = (term638 _127128 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6938116) (@lem6938115 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938118 {_127128 : Type'} (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term487 _127128 _92447 _92449 _92448) = (term487 _127128 _92447 _92449 _92448).
Proof. exact (eq_refl (term487 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938119 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term635 _127128 _92450 _92447 _92449 _92448) = (term639 _127128 _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938117 _127128 _92447 _92448 _92450) (@lem6938118 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938120 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term634 _127128 _92450 _92447 _92449 _92448) = (term639 _127128 _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938112 _127128 _92450 _92447 _92449 _92448) (@lem6938119 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938121 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term631 _127128 _92450 _92447 _92449 _92448) = (term640 _127128 _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938109 _127128 _92450 _92449) (@lem6938120 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938122 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term630 _127128 _92450 _92447 _92449 _92448) = (term640 _127128 _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938104 _127128 _92450 _92447 _92449 _92448) (@lem6938121 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938123 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term627 _127128 _92450 _92447 _92449 _92448) = (term641 _127128 _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938101 _127128 _92449) (@lem6938122 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938124 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term626 _127128 _92450 _92447 _92449 _92448) = (term641 _127128 _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938096 _127128 _92450 _92447 _92449 _92448) (@lem6938123 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938125 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6938126 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term642 _127128 _92450 _92447 _92449 _92448) = (term643 _127128 _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938125) (@lem6938124 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938127 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term461 _127128 x'' _92447 _92448 _92449) = (term461 _127128 x'' _92447 _92448 _92449).
Proof. exact (eq_refl (term461 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938128 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term623 _127128 _92450 x'' _92447 _92448 _92449) = (term644 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938126 _127128 _92450 _92447 _92449 _92448) (@lem6938127 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938129 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term612 _127128 x'' _92450 _92447 _92449 _92448) = (term644 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938093 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938128 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938131 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term645 _127128 x f s g.
Proof. exact (conj (@lem6937848 _127128 x f s g h1 h2 h3) (@lem6937855 _127128 f s g h3)). Qed.
Lemma lem6938132 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term646 _127128 x f s g.
Proof. exact (conj (@lem6937775 _127128 s x h1 h2) (@lem6938131 _127128 x f s g h1 h2 h3)). Qed.
Lemma lem6938133 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term647 _127128 x f s g.
Proof. exact (conj (@lem6937749 _127128 f s g h3) (@lem6938132 _127128 x f s g h1 h2 h3)). Qed.
Lemma lem6938135 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term644 _127128 _92450 x'' _92447 _92448 _92449.
Proof. exact (EQ_MP (@lem6938129 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938090 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6938136 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term644 _127128 _92450 x'' _92447 _92448 _92449.
Proof. exact (@lem6938135 _127128 _92450 _92447 _92448 _92449 x'' h1). Qed.
Lemma lem6938137 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term648 _127128 x x'' f g s.
Proof. exact (@lem6938136 _127128 (@I ((_127128 -> Prop) -> _127128) x s) f g s x'' h1). Qed.
Lemma lem6938140 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term461 _127128 x'' f g s.
Proof. exact (@lem6938137 _127128 x f g s x'' h1 (@lem6938133 _127128 x f s g h2 h3 h4)). Qed.
Lemma lem6938141 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term649 _127128 x'' f g s.
Proof. exact (fun h0 : term650 _127128 x'' f g s => @lem6938140 _127128 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem6938143 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938144 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term649 _127128 x'' f g s) = (term461 _127128 x'' f g s).
Proof. exact (@lem6938143 (term461 _127128 x'' f g s)). Qed.
Lemma lem6938145 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term461 _127128 x'' f g s.
Proof. exact (EQ_MP (@lem6938144 _127128 x'' f g s) (@lem6938141 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938147 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term606 _127128 s f g _92451.
Proof. exact (EQ_MP (@lem6937835 _127128 s f g _92451) (@lem6937824 _127128 _92451 f s g h1)). Qed.
Lemma lem6938148 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term606 _127128 s f g _92451.
Proof. exact (@lem6938147 _127128 _92451 f s g h1). Qed.
Lemma lem6938149 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term651 _127128 x'' f g s.
Proof. exact (@lem6938148 _127128 (term439 _127128 x'' f g s) f s g h1). Qed.
Lemma lem6938152 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term652 _127128 x'' f g s.
Proof. exact (@lem6938149 _127128 x'' f s g h4 (@lem6938145 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938153 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term653 _127128 x'' f g s.
Proof. exact (fun h0 : term654 _127128 x'' f g s => @lem6938152 _127128 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem6938155 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938156 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term653 _127128 x'' f g s) = (term652 _127128 x'' f g s).
Proof. exact (@lem6938155 (term652 _127128 x'' f g s)). Qed.
Lemma lem6938157 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term29 _127128 s) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term652 _127128 x'' f g s.
Proof. exact (EQ_MP (@lem6938156 _127128 x'' f g s) (@lem6938153 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938163 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6938164 (_92441 : nat) (_92442 : nat) : (term390 _92441 _92442) = (term655 _92441 _92442).
Proof. exact (@lem6938163 (term384 _92441 _92442) (term387 _92441 _92442)). Qed.
Lemma lem6938170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6938171 (_92441 : nat) (_92442 : nat) : (term656 _92441 _92442) = (term657 _92441 _92442).
Proof. exact (MK_COMB (@lem6938170) (@lem6938164 _92441 _92442)). Qed.
Lemma lem6938177 (_92441 : nat) (_92442 : nat) : (term655 _92441 _92442) = (term655 _92441 _92442).
Proof. exact (eq_refl (term655 _92441 _92442)). Qed.
Lemma lem6938178 (_92441 : nat) (_92442 : nat) : ((term390 _92441 _92442) = (term655 _92441 _92442)) = ((term655 _92441 _92442) = (term655 _92441 _92442)).
Proof. exact (MK_COMB (@lem6938171 _92441 _92442) (@lem6938177 _92441 _92442)). Qed.
Lemma lem6938180 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6938181 (x : Prop) : (x = x) = True.
Proof. exact (@lem6938180 Prop x). Qed.
Lemma lem6938182 (_92441 : nat) (_92442 : nat) : ((term655 _92441 _92442) = (term655 _92441 _92442)) = True.
Proof. exact (@lem6938181 (term655 _92441 _92442)). Qed.
Lemma lem6938183 (_92441 : nat) (_92442 : nat) : ((term390 _92441 _92442) = (term655 _92441 _92442)) = True.
Proof. exact (TRANS (@lem6938178 _92441 _92442) (@lem6938182 _92441 _92442)). Qed.
Lemma lem6938184 (_92441 : nat) (_92442 : nat) : True = ((term390 _92441 _92442) = (term655 _92441 _92442)).
Proof. exact (SYM (@lem6938183 _92441 _92442)). Qed.
Lemma lem6938185 (_92441 : nat) (_92442 : nat) : (term390 _92441 _92442) = (term655 _92441 _92442).
Proof. exact (EQ_MP (@lem6938184 _92441 _92442) (@lem0)). Qed.
Lemma lem6938186 (_92441 : nat) (_92442 : nat) (h1 : term38) : term655 _92441 _92442.
Proof. exact (EQ_MP (@lem6938185 _92441 _92442) (@lem6937287 _92441 _92442 h1)). Qed.
Lemma lem6938188 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6938189 (_92441 : nat) (_92442 : nat) : (term655 _92441 _92442) = (term658 _92441 _92442).
Proof. exact (@lem6938188 (term387 _92441 _92442) (term384 _92441 _92442)). Qed.
Lemma lem6938191 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938192 (_92441 : nat) (_92442 : nat) : (term659 _92441 _92442) = (term385 _92441 _92442).
Proof. exact (@lem6938191 (term385 _92441 _92442)). Qed.
Lemma lem6938193 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6938194 (_92441 : nat) (_92442 : nat) : (term660 _92441 _92442) = (term661 _92441 _92442).
Proof. exact (MK_COMB (@lem6938193) (@lem6938192 _92441 _92442)). Qed.
Lemma lem6938195 (_92441 : nat) (_92442 : nat) : (term384 _92441 _92442) = (term384 _92441 _92442).
Proof. exact (eq_refl (term384 _92441 _92442)). Qed.
Lemma lem6938196 (_92441 : nat) (_92442 : nat) : (term658 _92441 _92442) = (term662 _92441 _92442).
Proof. exact (MK_COMB (@lem6938194 _92441 _92442) (@lem6938195 _92441 _92442)). Qed.
Lemma lem6938197 (_92441 : nat) (_92442 : nat) : (term655 _92441 _92442) = (term662 _92441 _92442).
Proof. exact (TRANS (@lem6938189 _92441 _92442) (@lem6938196 _92441 _92442)). Qed.
Lemma lem6938200 (_92441 : nat) (_92442 : nat) (h1 : term38) : term662 _92441 _92442.
Proof. exact (EQ_MP (@lem6938197 _92441 _92442) (@lem6938186 _92441 _92442 h1)). Qed.
Lemma lem6938201 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) (h1 : term38) : term663 _127128 x'' f g s.
Proof. exact (@lem6938200 (term442 _127128 x'' f g s) (term445 _127128 x'' f g s) h1). Qed.
Lemma lem6938204 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term452 _127128 x'' f g s.
Proof. exact (@lem6938201 _127128 x'' f g s h2 (@lem6938157 _127128 x'' x f s g h1 h3 h4 h5)). Qed.
Lemma lem6938205 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term664 _127128 x'' f g s.
Proof. exact (fun h0 : term454 _127128 x'' f g s => @lem6938204 _127128 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem6938207 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938208 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (s : _127128 -> Prop) : (term664 _127128 x'' f g s) = (term452 _127128 x'' f g s).
Proof. exact (@lem6938207 (term452 _127128 x'' f g s)). Qed.
Lemma lem6938209 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term452 _127128 x'' f g s.
Proof. exact (EQ_MP (@lem6938208 _127128 x'' f g s) (@lem6938205 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938212 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (h1). Qed.
Lemma lem6938213 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term592 _127128 s.
Proof. exact (fun h0 : s = (@EMPTY _127128) => @lem6938212 _127128 s h1). Qed.
Lemma lem6938215 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6938216 {_127128 : Type'} (s : _127128 -> Prop) : (term592 _127128 s) = (term29 _127128 s).
Proof. exact (@lem6938215 (s = (@EMPTY _127128))). Qed.
Lemma lem6938217 {_127128 : Type'} (s : _127128 -> Prop) (h1 : term29 _127128 s) : term29 _127128 s.
Proof. exact (EQ_MP (@lem6938216 _127128 s) (@lem6938213 _127128 s h1)). Qed.
Lemma lem6938219 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (EQ_MP (@lem6937762 _127128 x _92452) (@lem6937305 _127128 _92452 x h1)). Qed.
Lemma lem6938220 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x _92452.
Proof. exact (@lem6938219 _127128 _92452 x h1). Qed.
Lemma lem6938221 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term595 _127128 x s.
Proof. exact (@lem6938220 _127128 s x h1). Qed.
Lemma lem6938224 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (@lem6938221 _127128 s x h2 (@lem6938217 _127128 s h1)). Qed.
Lemma lem6938225 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term596 _127128 x s.
Proof. exact (fun h0 : term597 _127128 x s => @lem6938224 _127128 s x h1 h2). Qed.
Lemma lem6938227 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938228 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term596 _127128 x s) = (term409 _127128 x s).
Proof. exact (@lem6938227 (term409 _127128 x s)). Qed.
Lemma lem6938229 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term29 _127128 s) (h2 : term380 _127128 x) : term409 _127128 x s.
Proof. exact (EQ_MP (@lem6938228 _127128 x s) (@lem6938225 _127128 s x h1 h2)). Qed.
Lemma lem6938231 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term487 _127128 f s g.
Proof. exact (proj2 (@lem6936847 _127128 f s g h1)). Qed.
Lemma lem6938232 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term611 _127128 f s g.
Proof. exact (fun h0 : term423 _127128 f s g => @lem6938231 _127128 f s g h1). Qed.
Lemma lem6938234 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6938235 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) : (term611 _127128 f s g) = (term487 _127128 f s g).
Proof. exact (@lem6938234 (term423 _127128 f s g)). Qed.
Lemma lem6938236 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term487 _127128 f s g.
Proof. exact (EQ_MP (@lem6938235 _127128 f s g) (@lem6938232 _127128 f s g h1)). Qed.
Lemma lem6938252 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938253 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term588 _127128 x'' _92450 _92447 _92449 _92448) = (term665 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6938252 (term396 _127128 _92450 _92449) (term454 _127128 x'' _92447 _92448 _92449) (term613 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938267 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938268 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term666 _127128 x'' _92450 _92447 _92449 _92448) = (term667 _127128 _92450 x'' _92447 _92449 _92448).
Proof. exact (@lem6938267 (term431 _127128 _92447 _92448 _92450) (term454 _127128 x'' _92447 _92448 _92449) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938282 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6938283 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term668 _127128 x'' _92447 _92449 _92448) = (term669 _127128 x'' _92447 _92448 _92449).
Proof. exact (@lem6938282 (term423 _127128 _92447 _92449 _92448) (term454 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938289 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term670 _127128 _92447 _92448 _92450) = (term670 _127128 _92447 _92448 _92450).
Proof. exact (eq_refl (term670 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938290 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term667 _127128 _92450 x'' _92447 _92449 _92448) = (term671 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938289 _127128 _92447 _92448 _92450) (@lem6938283 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938294 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938295 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term671 _127128 _92450 x'' _92447 _92448 _92449) = (term672 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938294 (term423 _127128 _92447 _92449 _92448) (term431 _127128 _92447 _92448 _92450) (term454 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938311 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term667 _127128 _92450 x'' _92447 _92449 _92448) = (term672 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938290 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938295 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938312 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term666 _127128 x'' _92450 _92447 _92449 _92448) = (term672 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938268 _127128 _92450 x'' _92447 _92449 _92448) (@lem6938311 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938313 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term433 _127128 _92450 _92449) = (term433 _127128 _92450 _92449).
Proof. exact (eq_refl (term433 _127128 _92450 _92449)). Qed.
Lemma lem6938314 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term665 _127128 x'' _92450 _92447 _92449 _92448) = (term673 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938313 _127128 _92450 _92449) (@lem6938312 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938318 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938319 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term673 _127128 _92450 x'' _92447 _92448 _92449) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938318 (term423 _127128 _92447 _92449 _92448) (term396 _127128 _92450 _92449) (term675 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938345 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term665 _127128 x'' _92450 _92447 _92449 _92448) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938314 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938319 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938346 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term588 _127128 x'' _92450 _92447 _92449 _92448) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938253 _127128 x'' _92450 _92447 _92449 _92448) (@lem6938345 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938347 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6938348 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term589 _127128 x'' _92450 _92447 _92449 _92448) = (term676 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938347 _127128 _92449) (@lem6938346 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938352 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938353 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term676 _127128 _92450 x'' _92447 _92448 _92449) = (term677 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938352 (term423 _127128 _92447 _92449 _92448) (term470 _127128 _92449) (term678 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938389 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term589 _127128 x'' _92450 _92447 _92449 _92448) = (term677 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938348 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938353 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6938391 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term679 _127128 x'' _92450 _92447 _92449 _92448) = (term680 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938390) (@lem6938389 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938395 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938396 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term681 _127128 x'' _92450 _92447 _92449 _92448) = (term682 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6938395 (term470 _127128 _92449) (term431 _127128 _92447 _92448 _92450) (term683 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938420 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938421 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term683 _127128 x'' _92450 _92447 _92449 _92448) = (term684 _127128 _92450 x'' _92447 _92449 _92448).
Proof. exact (@lem6938420 (term396 _127128 _92450 _92449) (term454 _127128 x'' _92447 _92448 _92449) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6938436 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term668 _127128 x'' _92447 _92449 _92448) = (term669 _127128 x'' _92447 _92448 _92449).
Proof. exact (@lem6938435 (term423 _127128 _92447 _92449 _92448) (term454 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938442 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term433 _127128 _92450 _92449) = (term433 _127128 _92450 _92449).
Proof. exact (eq_refl (term433 _127128 _92450 _92449)). Qed.
Lemma lem6938443 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term684 _127128 _92450 x'' _92447 _92449 _92448) = (term685 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938442 _127128 _92450 _92449) (@lem6938436 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938447 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938448 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term685 _127128 _92450 x'' _92447 _92448 _92449) = (term686 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938447 (term423 _127128 _92447 _92449 _92448) (term396 _127128 _92450 _92449) (term454 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938464 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term684 _127128 _92450 x'' _92447 _92449 _92448) = (term686 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938443 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938448 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938465 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term683 _127128 x'' _92450 _92447 _92449 _92448) = (term686 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938421 _127128 _92450 x'' _92447 _92449 _92448) (@lem6938464 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938466 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term670 _127128 _92447 _92448 _92450) = (term670 _127128 _92447 _92448 _92450).
Proof. exact (eq_refl (term670 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938467 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term687 _127128 x'' _92450 _92447 _92449 _92448) = (term688 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938466 _127128 _92447 _92448 _92450) (@lem6938465 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938471 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938472 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term688 _127128 _92450 x'' _92447 _92448 _92449) = (term689 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938471 (term423 _127128 _92447 _92449 _92448) (term431 _127128 _92447 _92448 _92450) (term690 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938486 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938487 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term691 _127128 _92450 x'' _92447 _92448 _92449) = (term678 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938486 (term396 _127128 _92450 _92449) (term431 _127128 _92447 _92448 _92450) (term454 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938503 {_127128 : Type'} (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term692 _127128 _92447 _92449 _92448) = (term692 _127128 _92447 _92449 _92448).
Proof. exact (eq_refl (term692 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938504 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term689 _127128 _92450 x'' _92447 _92448 _92449) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938503 _127128 _92447 _92449 _92448) (@lem6938487 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938515 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term688 _127128 _92450 x'' _92447 _92448 _92449) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938472 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938504 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938516 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term687 _127128 x'' _92450 _92447 _92449 _92448) = (term674 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938467 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938515 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938517 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term471 _127128 _92449) = (term471 _127128 _92449).
Proof. exact (eq_refl (term471 _127128 _92449)). Qed.
Lemma lem6938518 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term682 _127128 x'' _92450 _92447 _92449 _92448) = (term676 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938517 _127128 _92449) (@lem6938516 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938522 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6938523 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term676 _127128 _92450 x'' _92447 _92448 _92449) = (term677 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (@lem6938522 (term423 _127128 _92447 _92449 _92448) (term470 _127128 _92449) (term678 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938559 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term682 _127128 x'' _92450 _92447 _92449 _92448) = (term677 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938518 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938523 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938560 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term681 _127128 x'' _92450 _92447 _92449 _92448) = (term677 _127128 _92450 x'' _92447 _92448 _92449).
Proof. exact (TRANS (@lem6938396 _127128 x'' _92450 _92447 _92449 _92448) (@lem6938559 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938561 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : ((term589 _127128 x'' _92450 _92447 _92449 _92448) = (term681 _127128 x'' _92450 _92447 _92449 _92448)) = ((term677 _127128 _92450 x'' _92447 _92448 _92449) = (term677 _127128 _92450 x'' _92447 _92448 _92449)).
Proof. exact (MK_COMB (@lem6938391 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938560 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938563 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6938564 (x : Prop) : (x = x) = True.
Proof. exact (@lem6938563 Prop x). Qed.
Lemma lem6938565 {_127128 : Type'} (_92450 : _127128) (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : ((term677 _127128 _92450 x'' _92447 _92448 _92449) = (term677 _127128 _92450 x'' _92447 _92448 _92449)) = True.
Proof. exact (@lem6938564 (term677 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938566 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : ((term589 _127128 x'' _92450 _92447 _92449 _92448) = (term681 _127128 x'' _92450 _92447 _92449 _92448)) = True.
Proof. exact (TRANS (@lem6938561 _127128 _92450 x'' _92447 _92448 _92449) (@lem6938565 _127128 _92450 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938567 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : True = ((term589 _127128 x'' _92450 _92447 _92449 _92448) = (term681 _127128 x'' _92450 _92447 _92449 _92448)).
Proof. exact (SYM (@lem6938566 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938568 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term589 _127128 x'' _92450 _92447 _92449 _92448) = (term681 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (EQ_MP (@lem6938567 _127128 x'' _92450 _92447 _92449 _92448) (@lem0)). Qed.
Lemma lem6938569 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term681 _127128 x'' _92450 _92447 _92449 _92448.
Proof. exact (EQ_MP (@lem6938568 _127128 x'' _92450 _92447 _92449 _92448) (@lem6937359 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6938571 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6938572 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term681 _127128 x'' _92450 _92447 _92449 _92448) = (term693 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (@lem6938571 (term694 _127128 x'' _92450 _92447 _92449 _92448) (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938574 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938575 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term695 _127128 x'' _92450 _92447 _92449 _92448) = (term696 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6938574 (term470 _127128 _92449) (term683 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938577 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938578 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term628 _127128 _92449) = (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) _92449).
Proof. exact (@lem6938577 (@I ((_127128 -> Prop) -> Prop) (@FINITE _127128) _92449)). Qed.
Lemma lem6938579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938580 {_127128 : Type'} (_92449 : _127128 -> Prop) : (term629 _127128 _92449) = (term492 _127128 _92449).
Proof. exact (MK_COMB (@lem6938579) (@lem6938578 _127128 _92449)). Qed.
Lemma lem6938582 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938583 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term697 _127128 x'' _92450 _92447 _92449 _92448) = (term698 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (@lem6938582 (term454 _127128 x'' _92447 _92448 _92449) (term699 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938585 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938586 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term700 _127128 x'' _92447 _92448 _92449) = (term452 _127128 x'' _92447 _92448 _92449).
Proof. exact (@lem6938585 (term452 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938588 {_127128 : Type'} (x'' : type695 _127128) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92449 : _127128 -> Prop) : (term701 _127128 x'' _92447 _92448 _92449) = (term702 _127128 x'' _92447 _92448 _92449).
Proof. exact (MK_COMB (@lem6938587) (@lem6938586 _127128 x'' _92447 _92448 _92449)). Qed.
Lemma lem6938590 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6938591 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term703 _127128 _92450 _92447 _92449 _92448) = (term704 _127128 _92450 _92447 _92449 _92448).
Proof. exact (@lem6938590 (term396 _127128 _92450 _92449) (term423 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938593 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6938594 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term603 _127128 _92450 _92449) = (term395 _127128 _92450 _92449).
Proof. exact (@lem6938593 (term395 _127128 _92450 _92449)). Qed.
Lemma lem6938595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938596 {_127128 : Type'} (_92450 : _127128) (_92449 : _127128 -> Prop) : (term632 _127128 _92450 _92449) = (term633 _127128 _92450 _92449).
Proof. exact (MK_COMB (@lem6938595) (@lem6938594 _127128 _92450 _92449)). Qed.
Lemma lem6938597 {_127128 : Type'} (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term487 _127128 _92447 _92449 _92448) = (term487 _127128 _92447 _92449 _92448).
Proof. exact (eq_refl (term487 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938598 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term704 _127128 _92450 _92447 _92449 _92448) = (term705 _127128 _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938596 _127128 _92450 _92449) (@lem6938597 _127128 _92447 _92449 _92448)). Qed.
Lemma lem6938599 {_127128 : Type'} (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term703 _127128 _92450 _92447 _92449 _92448) = (term705 _127128 _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938591 _127128 _92450 _92447 _92449 _92448) (@lem6938598 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938600 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term698 _127128 x'' _92450 _92447 _92449 _92448) = (term706 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938588 _127128 x'' _92447 _92448 _92449) (@lem6938599 _127128 _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938601 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term697 _127128 x'' _92450 _92447 _92449 _92448) = (term706 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938583 _127128 x'' _92450 _92447 _92449 _92448) (@lem6938600 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938602 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term696 _127128 x'' _92450 _92447 _92449 _92448) = (term707 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938580 _127128 _92449) (@lem6938601 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938603 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term695 _127128 x'' _92450 _92447 _92449 _92448) = (term707 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (TRANS (@lem6938575 _127128 x'' _92450 _92447 _92449 _92448) (@lem6938602 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6938605 {_127128 : Type'} (x'' : type695 _127128) (_92450 : _127128) (_92447 : _127128 -> nat) (_92449 : _127128 -> Prop) (_92448 : _127128 -> nat) : (term708 _127128 x'' _92450 _92447 _92449 _92448) = (term709 _127128 x'' _92450 _92447 _92449 _92448).
Proof. exact (MK_COMB (@lem6938604) (@lem6938603 _127128 x'' _92450 _92447 _92449 _92448)). Qed.
Lemma lem6938606 {_127128 : Type'} (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term431 _127128 _92447 _92448 _92450) = (term431 _127128 _92447 _92448 _92450).
Proof. exact (eq_refl (term431 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938607 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term693 _127128 x'' _92449 _92447 _92448 _92450) = (term710 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (MK_COMB (@lem6938605 _127128 x'' _92450 _92447 _92449 _92448) (@lem6938606 _127128 _92447 _92448 _92450)). Qed.
Lemma lem6938608 {_127128 : Type'} (x'' : type695 _127128) (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) : (term681 _127128 x'' _92450 _92447 _92449 _92448) = (term710 _127128 x'' _92449 _92447 _92448 _92450).
Proof. exact (TRANS (@lem6938572 _127128 x'' _92449 _92447 _92448 _92450) (@lem6938607 _127128 x'' _92449 _92447 _92448 _92450)). Qed.
Lemma lem6938610 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term29 _127128 s) (h2 : term380 _127128 x) (h3 : term80 _127128 f s g) : term711 _127128 x f s g.
Proof. exact (conj (@lem6938229 _127128 s x h1 h2) (@lem6938236 _127128 f s g h3)). Qed.
Lemma lem6938611 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term712 _127128 x'' x f s g.
Proof. exact (conj (@lem6938209 _127128 x'' x f s g h1 h2 h3 h4 h5) (@lem6938610 _127128 x f s g h3 h4 h5)). Qed.
Lemma lem6938612 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term713 _127128 x'' x f s g.
Proof. exact (conj (@lem6937742 _127128 f s g h5) (@lem6938611 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938614 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term710 _127128 x'' _92449 _92447 _92448 _92450.
Proof. exact (EQ_MP (@lem6938608 _127128 x'' _92449 _92447 _92448 _92450) (@lem6938569 _127128 _92450 _92447 _92449 _92448 x'' h1)). Qed.
Lemma lem6938615 {_127128 : Type'} (_92449 : _127128 -> Prop) (_92447 : _127128 -> nat) (_92448 : _127128 -> nat) (_92450 : _127128) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term710 _127128 x'' _92449 _92447 _92448 _92450.
Proof. exact (@lem6938614 _127128 _92449 _92447 _92448 _92450 x'' h1). Qed.
Lemma lem6938616 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) (s : _127128 -> Prop) (x'' : type695 _127128) (h1 : term271 _127128 x'') : term714 _127128 x'' f g x s.
Proof. exact (@lem6938615 _127128 s f g (@I ((_127128 -> Prop) -> _127128) x s) x'' h1). Qed.
Lemma lem6938619 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term610 _127128 f g x s.
Proof. exact (@lem6938616 _127128 f g x s x'' h1 (@lem6938612 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938620 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term715 _127128 f g x s.
Proof. exact (fun h0 : term608 _127128 f g x s => @lem6938619 _127128 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem6938622 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6938623 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) (s : _127128 -> Prop) : (term715 _127128 f g x s) = (term610 _127128 f g x s).
Proof. exact (@lem6938622 (term608 _127128 f g x s)). Qed.
Lemma lem6938624 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term610 _127128 f g x s.
Proof. exact (EQ_MP (@lem6938623 _127128 f g x s) (@lem6938620 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938626 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6938629 {_127128 : Type'} (f : _127128 -> nat) (g : _127128 -> nat) (_92451 : _127128) (s : _127128 -> Prop) : (term488 _127128 s f g _92451) = (term716 _127128 f g _92451 s).
Proof. exact (@lem6938626 (term429 _127128 f g _92451) (term396 _127128 _92451 s)). Qed.
Lemma lem6938632 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term716 _127128 f g _92451 s.
Proof. exact (EQ_MP (@lem6938629 _127128 f g _92451 s) (@lem6937299 _127128 _92451 f s g h1)). Qed.
Lemma lem6938633 {_127128 : Type'} (_92451 : _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term716 _127128 f g _92451 s.
Proof. exact (@lem6938632 _127128 _92451 f s g h1). Qed.
Lemma lem6938634 {_127128 : Type'} (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term717 _127128 f g x s.
Proof. exact (@lem6938633 _127128 (@I ((_127128 -> Prop) -> _127128) x s) f s g h1). Qed.
Lemma lem6938637 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term597 _127128 x s.
Proof. exact (@lem6938634 _127128 x f s g h5 (@lem6938624 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938638 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term718 _127128 x s.
Proof. exact (fun h0 : term409 _127128 x s => @lem6938637 _127128 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem6938640 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6938641 {_127128 : Type'} (x : type684 _127128) (s : _127128 -> Prop) : (term718 _127128 x s) = (term597 _127128 x s).
Proof. exact (@lem6938640 (term409 _127128 x s)). Qed.
Lemma lem6938642 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : term597 _127128 x s.
Proof. exact (EQ_MP (@lem6938641 _127128 x s) (@lem6938638 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938648 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6938649 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term412 _127128 x _92452) = (term719 _127128 x _92452).
Proof. exact (@lem6938648 (_92452 = (@EMPTY _127128)) (term409 _127128 x _92452)). Qed.
Lemma lem6938657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6938658 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term720 _127128 x _92452) = (term721 _127128 x _92452).
Proof. exact (MK_COMB (@lem6938657) (@lem6938649 _127128 x _92452)). Qed.
Lemma lem6938666 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term719 _127128 x _92452) = (term719 _127128 x _92452).
Proof. exact (eq_refl (term719 _127128 x _92452)). Qed.
Lemma lem6938667 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : ((term412 _127128 x _92452) = (term719 _127128 x _92452)) = ((term719 _127128 x _92452) = (term719 _127128 x _92452)).
Proof. exact (MK_COMB (@lem6938658 _127128 x _92452) (@lem6938666 _127128 x _92452)). Qed.
Lemma lem6938669 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6938670 (x : Prop) : (x = x) = True.
Proof. exact (@lem6938669 Prop x). Qed.
Lemma lem6938671 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : ((term719 _127128 x _92452) = (term719 _127128 x _92452)) = True.
Proof. exact (@lem6938670 (term719 _127128 x _92452)). Qed.
Lemma lem6938672 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : ((term412 _127128 x _92452) = (term719 _127128 x _92452)) = True.
Proof. exact (TRANS (@lem6938667 _127128 x _92452) (@lem6938671 _127128 x _92452)). Qed.
Lemma lem6938673 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : True = ((term412 _127128 x _92452) = (term719 _127128 x _92452)).
Proof. exact (SYM (@lem6938672 _127128 x _92452)). Qed.
Lemma lem6938674 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term412 _127128 x _92452) = (term719 _127128 x _92452).
Proof. exact (EQ_MP (@lem6938673 _127128 x _92452) (@lem0)). Qed.
Lemma lem6938675 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term719 _127128 x _92452.
Proof. exact (EQ_MP (@lem6938674 _127128 x _92452) (@lem6937305 _127128 _92452 x h1)). Qed.
Lemma lem6938677 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6938680 {_127128 : Type'} (x : type684 _127128) (_92452 : _127128 -> Prop) : (term719 _127128 x _92452) = (term722 _127128 x _92452).
Proof. exact (@lem6938677 (term409 _127128 x _92452) (_92452 = (@EMPTY _127128))). Qed.
Lemma lem6938683 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term722 _127128 x _92452.
Proof. exact (EQ_MP (@lem6938680 _127128 x _92452) (@lem6938675 _127128 _92452 x h1)). Qed.
Lemma lem6938684 {_127128 : Type'} (_92452 : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term722 _127128 x _92452.
Proof. exact (@lem6938683 _127128 _92452 x h1). Qed.
Lemma lem6938685 {_127128 : Type'} (s : _127128 -> Prop) (x : type684 _127128) (h1 : term380 _127128 x) : term722 _127128 x s.
Proof. exact (@lem6938684 _127128 s x h1). Qed.
Lemma lem6938688 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term29 _127128 s) (h4 : term380 _127128 x) (h5 : term80 _127128 f s g) : s = (@EMPTY _127128).
Proof. exact (@lem6938685 _127128 s x h4 (@lem6938642 _127128 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem6938689 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term723 _127128 s.
Proof. exact (fun h0 : term29 _127128 s => @lem6938688 _127128 x'' x f s g h1 h2 h0 h3 h4). Qed.
Lemma lem6938691 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938692 {_127128 : Type'} (s : _127128 -> Prop) : (term723 _127128 s) = (s = (@EMPTY _127128)).
Proof. exact (@lem6938691 (s = (@EMPTY _127128))). Qed.
Lemma lem6938693 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : s = (@EMPTY _127128).
Proof. exact (EQ_MP (@lem6938692 _127128 s) (@lem6938689 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938696 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6938698 {_127128 : Type'} (s : _127128 -> Prop) : (term29 _127128 s) = (term724 _127128 s).
Proof. exact (@lem6938696 (s = (@EMPTY _127128))). Qed.
Lemma lem6938701 {_127128 : Type'} (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term80 _127128 f s g) : term724 _127128 s.
Proof. exact (EQ_MP (@lem6938698 _127128 s) (@lem6937293 _127128 f s g h1)). Qed.
Lemma lem6938704 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : False.
Proof. exact (@lem6938701 _127128 f s g h4 (@lem6938693 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938705 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : term725.
Proof. exact (fun h0 : ~ False => @lem6938704 _127128 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem6938707 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6938708 : term725 = False.
Proof. exact (@lem6938707 False). Qed.
Lemma lem6938709 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (f : _127128 -> nat) (s : _127128 -> Prop) (g : _127128 -> nat) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term380 _127128 x) (h4 : term80 _127128 f s g) : False.
Proof. exact (EQ_MP (@lem6938708) (@lem6938705 _127128 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem6938710 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (g : _127128 -> nat) (x : type684 _127128) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term90 _127128 f g) (h4 : term380 _127128 x) : False.
Proof. exact (ex_elim (@lem6936069 _127128 f g h3) (fun s : _127128 -> Prop => fun h0 : term89 _127128 f g s => @lem6938709 _127128 x'' x f s g h1 h2 h4 h0)). Qed.
Lemma lem6938711 {_127128 : Type'} (x'' : type695 _127128) (f : _127128 -> nat) (x : type684 _127128) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term99 _127128 f) (h4 : term380 _127128 x) : False.
Proof. exact (ex_elim (@lem6936068 _127128 f h3) (fun g : _127128 -> nat => fun h0 : term98 _127128 f g => @lem6938710 _127128 x'' f g x h1 h2 h0 h4)). Qed.
Lemma lem6938712 {_127128 : Type'} (x'' : type695 _127128) (x : type684 _127128) (h1 : term271 _127128 x'') (h2 : term38) (h3 : term10 _127128) (h4 : term380 _127128 x) : False.
Proof. exact (ex_elim (@lem6934952 _127128 h3) (fun f : _127128 -> nat => fun h0 : term104 _127128 f => @lem6938711 _127128 x'' f x h1 h2 h0 h4)). Qed.
Lemma lem6938713 {_127128 : Type'} (x : type684 _127128) (h1 : term12 _127128) (h2 : term38) (h3 : term10 _127128) (h4 : term380 _127128 x) : False.
Proof. exact (ex_elim (@lem6935346 _127128 h1) (fun x'' : type695 _127128 => fun h0 : term273 _127128 x'' => @lem6938712 _127128 x'' x h0 h2 h3 h4)). Qed.
Lemma lem6938714 {_127128 A : Type'} (x : type684 _127128) (h1 : term12 _127128) (h2 : term12 A) (h3 : term38) (h4 : term10 _127128) (h5 : term380 _127128 x) : False.
Proof. exact (ex_elim (@lem6935740 A h2) (fun x' : type695 A => fun h0 : term273 A x' => @lem6938713 _127128 x h1 h3 h4 h5)). Qed.
Lemma lem6938715 {_127128 A : Type'} (h1 : term11 _127128) (h2 : term12 _127128) (h3 : term12 A) (h4 : term38) (h5 : term10 _127128) : False.
Proof. exact (ex_elim (@lem6936064 _127128 h1) (fun x : type684 _127128 => fun h0 : term382 _127128 x => @lem6938714 _127128 A x h2 h3 h4 h5 h0)). Qed.
Lemma lem6938716 {_127128 A : Type'} (h1 : term12 _127128) (h2 : term12 A) (h3 : term38) (h4 : term10 _127128) : term17 _127128.
Proof. exact (fun h0 : term11 _127128 => @lem6938715 _127128 A h0 h1 h2 h3 h4). Qed.
Lemma lem6938717 {_127128 : Type'} : (term17 _127128) = (term18 _127128).
Proof. exact (@lem69 (term11 _127128)). Qed.
Lemma lem6938718 {_127128 A : Type'} (h1 : term12 _127128) (h2 : term12 A) (h3 : term38) (h4 : term10 _127128) : term18 _127128.
Proof. exact (EQ_MP (@lem6938717 _127128) (@lem6938716 _127128 A h1 h2 h3 h4)). Qed.
Lemma lem6938719 {_127128 A : Type'} (h1 : term12 _127128) (h2 : term12 A) (h3 : term10 _127128) : term21 _127128.
Proof. exact (fun h0 : term38 => @lem6938718 _127128 A h1 h2 h0 h3). Qed.
Lemma lem6938720 {_127128 A : Type'} (h1 : term12 _127128) (h2 : term10 _127128) : term24 _127128 A.
Proof. exact (fun h0 : term12 A => @lem6938719 _127128 A h1 h0 h2). Qed.
Lemma lem6938721 {_127128 A : Type'} (h1 : term10 _127128) : term26 _127128 A.
Proof. exact (fun h0 : term12 _127128 => @lem6938720 _127128 A h0 h1). Qed.
Lemma lem6938722 {_127128 A : Type'} : term28 _127128 A.
Proof. exact (fun h0 : term10 _127128 => @lem6938721 _127128 A h0). Qed.
Lemma lem6938723 {_127128 A : Type'} : term13 _127128 A.
Proof. exact (EQ_MP (@lem6934784 _127128 A) (@lem6938722 _127128 A)). Qed.
Lemma lem6938725 {_127128 A : Type'} : term13 _127128 A.
Proof. exact (@lem6934270 _127128 A (@lem6938723 _127128 A)). Qed.
Lemma lem6938726 {_127128 A : Type'} (h1 : term10 _127128) : term25 _127128 A.
Proof. exact (@lem6938725 _127128 A (@lem6934248 _127128 h1)). Qed.
Lemma lem6938727 {_127128 A : Type'} (h1 : term10 _127128) : term23 _127128 A.
Proof. exact (@lem6938726 _127128 A h1 (@lem6934252 _127128)). Qed.
Lemma lem6938728 {_127128 : Type'} (h1 : term10 _127128) : term20 _127128.
Proof. exact (@lem6938727 _127128 Prop h1 (@lem6934233 Prop)). Qed.
Lemma lem6938729 {_127128 : Type'} (h1 : term10 _127128) : term17 _127128.
Proof. exact (@lem6938728 _127128 h1 (@lem98439)). Qed.
Lemma lem6938730 {_127128 : Type'} (h1 : term10 _127128) : False.
Proof. exact (@lem6938729 _127128 h1 (@lem6934249 _127128)). Qed.
Lemma lem6938731 {_127128 : Type'} (h1 : term10 _127128) : (term10 _127128) = False.
Proof. exact (prop_ext (fun h2 : term10 _127128 => @lem6938730 _127128 h1) (fun h2 : False => @lem6934248 _127128 h1)). Qed.
Lemma lem6938732 {_127128 : Type'} (h1 : term10 _127128) : False.
Proof. exact (EQ_MP (@lem6938731 _127128 h1) (@lem6934248 _127128 h1)). Qed.
Lemma lem6938733 {_127128 : Type'} : term9 _127128.
Proof. exact (fun h0 : term10 _127128 => @lem6938732 _127128 h0). Qed.
Lemma lem6938734 {_127128 : Type'} : term8 _127128.
Proof. exact (EQ_MP (@lem6934247 _127128) (@lem6938733 _127128)). Qed.
