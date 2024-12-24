Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_UNIQUE_term_abbrevs.
Require Import CART_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LAMBDA_BETA_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7622315 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7622316 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7622317 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7622316 t1) (@lem7622315 t1)). Qed.
Lemma lem7622318 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7622317 t1 t2). Qed.
Lemma lem7622319 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7622320 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7622319 t1 t2) (@lem7622318 t1 t2)). Qed.
Lemma lem7622321 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7622320 t1 t2 t3). Qed.
Lemma lem7622322 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7622323 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7622322 t1 t2 t3) (@lem7622321 t1 t2 t3)). Qed.
Lemma lem7622324 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7622323 t1 t2 t3)). Qed.
Lemma lem7622325 {A B : Type'} (g : nat -> A) (i : nat) : term7 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7622326 {A B : Type'} (g : nat -> A) (i : nat) : (term7 A B g i) = (term8 A B g i).
Proof. exact (eq_refl (term7 A B g i)). Qed.
Lemma lem7622327 {A B : Type'} (g : nat -> A) (i : nat) : term8 A B g i.
Proof. exact (EQ_MP (@lem7622326 A B g i) (@lem7622325 A B g i)). Qed.
Lemma lem7622328 {B : Type'} (i : nat) (h1 : term9 B i) : term9 B i.
Proof. exact (h1). Qed.
Lemma lem7622329 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term9 B i) : (term10 A B g i) = (g i).
Proof. exact (@lem7622327 A B g i (@lem7622328 B i h1)). Qed.
Lemma lem7622335 {A B : Type'} (x : cart A B) : term11 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7622336 {A B : Type'} (x : cart A B) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem7622337 {A B : Type'} (x : cart A B) : term12 A B x.
Proof. exact (EQ_MP (@lem7622336 A B x) (@lem7622335 A B x)). Qed.
Lemma lem7622338 {A B : Type'} (x : cart A B) (y : cart A B) : term13 A B x y.
Proof. exact (@lem7622337 A B x y). Qed.
Lemma lem7622339 {A B : Type'} (x : cart A B) (y : cart A B) : (term13 A B x y) = ((x = y) = (term14 A B x y)).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem7622399 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term14 A B x y).
Proof. exact (EQ_MP (@lem7622339 A B x y) (@lem7622338 A B x y)). Qed.
Lemma lem7622400 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term14 A B x y).
Proof. exact (@lem7622399 A B x y). Qed.
Lemma lem7622401 {A B : Type'} (g : nat -> A) (f : cart A B) : ((@lambda A B g) = f) = (term15 A B g f).
Proof. exact (@lem7622400 A B (@lambda A B g) f). Qed.
Lemma lem7622409 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7622410 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem7622409 p q p' q'). Qed.
Lemma lem7622411 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem7622410 p q p'). Qed.
Lemma lem7622412 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : term19 A B g f i.
Proof. exact (@lem7622411 (term9 B i) ((term10 A B g i) = (@dollar A B f i))). Qed.
Lemma lem7622413 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) : term20 A B g f i p'.
Proof. exact (@lem7622412 A B g f i p'). Qed.
Lemma lem7622414 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) : (term20 A B g f i p') = (term21 A B g f i p').
Proof. exact (eq_refl (term20 A B g f i p')). Qed.
Lemma lem7622415 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) : term21 A B g f i p'.
Proof. exact (EQ_MP (@lem7622414 A B g f i p') (@lem7622413 A B g f i p')). Qed.
Lemma lem7622416 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) (q' : Prop) : term22 A B g f i p' q'.
Proof. exact (@lem7622415 A B g f i p' q'). Qed.
Lemma lem7622417 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) (q' : Prop) : (term22 A B g f i p' q') = (term23 A B g f i p' q').
Proof. exact (eq_refl (term22 A B g f i p' q')). Qed.
Lemma lem7622418 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (p' : Prop) (q' : Prop) : term23 A B g f i p' q'.
Proof. exact (EQ_MP (@lem7622417 A B g f i p' q') (@lem7622416 A B g f i p' q')). Qed.
Lemma lem7622421 {B : Type'} (i : nat) : (term9 B i) = (term9 B i).
Proof. exact (eq_refl (term9 B i)). Qed.
Lemma lem7622422 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (q' : Prop) : term24 A B g f i q'.
Proof. exact (@lem7622418 A B g f i (term9 B i) q'). Qed.
Lemma lem7622423 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (q' : Prop) : term25 A B g f i q'.
Proof. exact (@lem7622422 A B g f i q' (@lem7622421 B i)). Qed.
Lemma lem7622424 {B : Type'} (i : nat) (h1 : term9 B i) : term9 B i.
Proof. exact (h1). Qed.
Lemma lem7622425 {B : Type'} (i : nat) (h1 : term9 B i) : term26 B i.
Proof. exact (proj2 (@lem7622424 B i h1)). Qed.
Lemma lem7622426 {B : Type'} (i : nat) : (term26 B i) = ((term26 B i) = True).
Proof. exact (@lem7 (term26 B i)). Qed.
Lemma lem7622428 {B : Type'} (i : nat) (h1 : term9 B i) : term27 i.
Proof. exact (proj1 (@lem7622424 B i h1)). Qed.
Lemma lem7622429 (i : nat) : (term27 i) = ((term27 i) = True).
Proof. exact (@lem7 (term27 i)). Qed.
Lemma lem7622436 {A B : Type'} (g : nat -> A) (i : nat) : term8 A B g i.
Proof. exact (fun h0 : term9 B i => @lem7622329 A B g i h0). Qed.
Lemma lem7622437 {A B : Type'} (g : nat -> A) (i : nat) : term8 A B g i.
Proof. exact (@lem7622436 A B g i). Qed.
Lemma lem7622441 {B : Type'} (i : nat) (h1 : term9 B i) : (term27 i) = True.
Proof. exact (EQ_MP (@lem7622429 i) (@lem7622428 B i h1)). Qed.
Lemma lem7622442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7622443 {B : Type'} (i : nat) (h1 : term9 B i) : (term28 i) = (and True).
Proof. exact (MK_COMB (@lem7622442) (@lem7622441 B i h1)). Qed.
Lemma lem7622445 {B : Type'} (i : nat) (h1 : term9 B i) : (term26 B i) = True.
Proof. exact (EQ_MP (@lem7622426 B i) (@lem7622425 B i h1)). Qed.
Lemma lem7622446 {B : Type'} (i : nat) (h1 : term9 B i) : (term9 B i) = (True /\ True).
Proof. exact (MK_COMB (@lem7622443 B i h1) (@lem7622445 B i h1)). Qed.
Lemma lem7622448 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7622449 : (True /\ True) = True.
Proof. exact (@lem7622448 True). Qed.
Lemma lem7622450 {B : Type'} (i : nat) (h1 : term9 B i) : (term9 B i) = True.
Proof. exact (TRANS (@lem7622446 B i h1) (@lem7622449)). Qed.
Lemma lem7622451 {B : Type'} (i : nat) (h1 : term9 B i) : True = (term9 B i).
Proof. exact (SYM (@lem7622450 B i h1)). Qed.
Lemma lem7622452 {B : Type'} (i : nat) (h1 : term9 B i) : term9 B i.
Proof. exact (EQ_MP (@lem7622451 B i h1) (@lem0)). Qed.
Lemma lem7622453 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term9 B i) : (term10 A B g i) = (g i).
Proof. exact (@lem7622437 A B g i (@lem7622452 B i h1)). Qed.
Lemma lem7622454 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7622455 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term9 B i) : (term29 A B g i) = (term30 A g i).
Proof. exact (MK_COMB (@lem7622454 A) (@lem7622453 A B g i h1)). Qed.
Lemma lem7622456 {A B : Type'} (f : cart A B) (i : nat) : (@dollar A B f i) = (@dollar A B f i).
Proof. exact (eq_refl (@dollar A B f i)). Qed.
Lemma lem7622457 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term9 B i) : ((term10 A B g i) = (@dollar A B f i)) = ((g i) = (@dollar A B f i)).
Proof. exact (MK_COMB (@lem7622455 A B g i h1) (@lem7622456 A B f i)). Qed.
Lemma lem7622462 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : term31 A B g f i.
Proof. exact (fun h0 : term9 B i => @lem7622457 A B g f i h0). Qed.
Lemma lem7622463 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : term32 A B g f i.
Proof. exact (@lem7622423 A B g f i ((g i) = (@dollar A B f i))). Qed.
Lemma lem7622464 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term33 A B g f i) = (term34 A B g f i).
Proof. exact (@lem7622463 A B g f i (@lem7622462 A B g f i)). Qed.
Lemma lem7622504 {A B : Type'} (g : nat -> A) (f : cart A B) : (term35 A B g f) = (term36 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7622464 A B g f i)). Qed.
Lemma lem7622544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7622545 {A B : Type'} (g : nat -> A) (f : cart A B) : (term15 A B g f) = (term37 A B g f).
Proof. exact (MK_COMB (@lem7622544) (@lem7622504 A B g f)). Qed.
Lemma lem7622589 {A B : Type'} (g : nat -> A) (f : cart A B) : ((@lambda A B g) = f) = (term37 A B g f).
Proof. exact (TRANS (@lem7622401 A B g f) (@lem7622545 A B g f)). Qed.
Lemma lem7622590 {A B : Type'} (f : cart A B) (g : nat -> A) : (term38 A B f g) = (term38 A B f g).
Proof. exact (eq_refl (term38 A B f g)). Qed.
Lemma lem7622591 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term39 A B f g) = ((@lambda A B g) = f)) = ((term39 A B f g) = (term37 A B g f)).
Proof. exact (MK_COMB (@lem7622590 A B f g) (@lem7622589 A B g f)). Qed.
Lemma lem7622682 {A B : Type'} (f : cart A B) : (term40 A B f) = (term41 A B f).
Proof. exact (fun_ext (fun g : nat -> A => @lem7622591 A B g f)). Qed.
Lemma lem7622773 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem7622774 {A B : Type'} (f : cart A B) : (term42 A B f) = (term43 A B f).
Proof. exact (MK_COMB (@lem7622773 A) (@lem7622682 A B f)). Qed.
Lemma lem7622869 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (fun_ext (fun f : cart A B => @lem7622774 A B f)). Qed.
Lemma lem7622964 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7622965 {A B : Type'} : (term46 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem7622964 A B) (@lem7622869 A B)). Qed.
Lemma lem7623064 {A B : Type'} : (term47 A B) = (term46 A B).
Proof. exact (SYM (@lem7622965 A B)). Qed.
Lemma lem7623066 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7623067 {A B : Type'} : (term47 A B) = (term49 A B).
Proof. exact (@lem7623066 (term47 A B)). Qed.
Lemma lem7623068 {A B : Type'} : (term49 A B) = (term47 A B).
Proof. exact (SYM (@lem7623067 A B)). Qed.
Lemma lem7623069 {A B : Type'} (h1 : term50 A B) : term50 A B.
Proof. exact (h1). Qed.
Lemma lem7623072 {A B : Type'} (h1 : term49 A B) : term49 A B.
Proof. exact (h1). Qed.
Lemma lem7623073 {A B : Type'} : term51 A B.
Proof. exact (fun h0 : term49 A B => @lem7623072 A B h0). Qed.
Lemma lem7623074 {A B : Type'} (h1 : term51 A B) : term51 A B.
Proof. exact (h1). Qed.
Lemma lem7623075 {A B : Type'} (h1 : term49 A B) : term49 A B.
Proof. exact (h1). Qed.
Lemma lem7623076 {A B : Type'} (h1 : term49 A B) (h2 : term51 A B) : term49 A B.
Proof. exact (@lem7623074 A B h2 (@lem7623075 A B h1)). Qed.
Lemma lem7623077 {A B : Type'} (h1 : term49 A B) : term52 A B.
Proof. exact (fun h0 : term51 A B => @lem7623076 A B h1 h0). Qed.
Lemma lem7623078 {A B : Type'} (h1 : term51 A B) : term51 A B.
Proof. exact (h1). Qed.
Lemma lem7623079 {A B : Type'} (h1 : term49 A B) (h2 : term51 A B) : term49 A B.
Proof. exact (@lem7623077 A B h1 (@lem7623078 A B h2)). Qed.
Lemma lem7623080 {A B : Type'} (h1 : term51 A B) : term51 A B.
Proof. exact (fun h0 : term49 A B => @lem7623079 A B h0 h1). Qed.
Lemma lem7623081 {A B : Type'} : term53 A B.
Proof. exact (fun h0 : term51 A B => @lem7623080 A B h0). Qed.
Lemma lem7623084 {A B : Type'} : term51 A B.
Proof. exact (@lem7623081 A B (@lem7623073 A B)). Qed.
Lemma lem7623085 {A B : Type'} : term51 A B.
Proof. exact (@lem7623084 A B). Qed.
Lemma lem7623087 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7623088 {A B : Type'} : (term49 A B) = (term54 A B).
Proof. exact (@lem7623087 (term50 A B)). Qed.
Lemma lem7623090 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7623091 {A B : Type'} : (term54 A B) = (term47 A B).
Proof. exact (@lem7623090 (term47 A B)). Qed.
Lemma lem7623120 {A B : Type'} : (term49 A B) = (term47 A B).
Proof. exact (TRANS (@lem7623088 A B) (@lem7623091 A B)). Qed.
Lemma lem7623129 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term34 A B g f i) = (term34 A B g f i).
Proof. exact (eq_refl (term34 A B g f i)). Qed.
Lemma lem7623130 {A B : Type'} (g : nat -> A) (f : cart A B) : (term36 A B g f) = (term36 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623129 A B g f i)). Qed.
Lemma lem7623131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623132 {A B : Type'} (g : nat -> A) (f : cart A B) : (term37 A B g f) = (term37 A B g f).
Proof. exact (MK_COMB (@lem7623131) (@lem7623130 A B g f)). Qed.
Lemma lem7623141 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term56 A B f g i) = (term56 A B f g i).
Proof. exact (eq_refl (term56 A B f g i)). Qed.
Lemma lem7623142 {A B : Type'} (f : cart A B) (g : nat -> A) : (term57 A B f g) = (term57 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623141 A B f g i)). Qed.
Lemma lem7623143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623144 {A B : Type'} (f : cart A B) (g : nat -> A) : (term39 A B f g) = (term39 A B f g).
Proof. exact (MK_COMB (@lem7623143) (@lem7623142 A B f g)). Qed.
Lemma lem7623145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7623146 {A B : Type'} (f : cart A B) (g : nat -> A) : (term38 A B f g) = (term38 A B f g).
Proof. exact (MK_COMB (@lem7623145) (@lem7623144 A B f g)). Qed.
Lemma lem7623147 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term39 A B f g) = (term37 A B g f)) = ((term39 A B f g) = (term37 A B g f)).
Proof. exact (MK_COMB (@lem7623146 A B f g) (@lem7623132 A B g f)). Qed.
Lemma lem7623148 {A B : Type'} (f : cart A B) : (term41 A B f) = (term41 A B f).
Proof. exact (fun_ext (fun g : nat -> A => @lem7623147 A B g f)). Qed.
Lemma lem7623149 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem7623150 {A B : Type'} (f : cart A B) : (term43 A B f) = (term43 A B f).
Proof. exact (MK_COMB (@lem7623149 A) (@lem7623148 A B f)). Qed.
Lemma lem7623151 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (fun_ext (fun f : cart A B => @lem7623150 A B f)). Qed.
Lemma lem7623152 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7623153 {A B : Type'} : (term47 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem7623152 A B) (@lem7623151 A B)). Qed.
Lemma lem7623188 {A B : Type'} : (term49 A B) = (term47 A B).
Proof. exact (TRANS (@lem7623120 A B) (@lem7623153 A B)). Qed.
Lemma lem7623189 {A B : Type'} : (term47 A B) = (term49 A B).
Proof. exact (SYM (@lem7623188 A B)). Qed.
Lemma lem7623191 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7623192 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term39 A B f g) = (term37 A B g f)) = (term58 A B g f).
Proof. exact (@lem7623191 ((term39 A B f g) = (term37 A B g f))). Qed.
Lemma lem7623193 {A B : Type'} (g : nat -> A) (f : cart A B) : (term58 A B g f) = ((term39 A B f g) = (term37 A B g f)).
Proof. exact (SYM (@lem7623192 A B g f)). Qed.
Lemma lem7623194 {A B : Type'} (g : nat -> A) (f : cart A B) (h1 : term59 A B g f) : term59 A B g f.
Proof. exact (h1). Qed.
Lemma lem7623203 {B : Type'} (i : nat) : (term60 B i) = (term61 B i).
Proof. exact (@lem17045 (term27 i) (term26 B i)). Qed.
Lemma lem7623208 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : ((@dollar A B f i) = (g i)) = ((@dollar A B f i) = (g i)).
Proof. exact (eq_refl ((@dollar A B f i) = (g i))). Qed.
Lemma lem7623213 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term62 A B f g i) = (term63 A B f g i).
Proof. exact (@lem17362 (term9 B i) ((@dollar A B f i) = (g i))). Qed.
Lemma lem7623214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623215 {B : Type'} (i : nat) : (term64 B i) = (term65 B i).
Proof. exact (MK_COMB (@lem7623214) (@lem7623203 B i)). Qed.
Lemma lem7623216 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term66 A B f g i) = (term67 A B f g i).
Proof. exact (MK_COMB (@lem7623215 B i) (@lem7623208 A B f g i)). Qed.
Lemma lem7623217 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term56 A B f g i) = (term66 A B f g i).
Proof. exact (@lem17265 (term9 B i) ((@dollar A B f i) = (g i))). Qed.
Lemma lem7623218 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term56 A B f g i) = (term67 A B f g i).
Proof. exact (TRANS (@lem7623217 A B f g i) (@lem7623216 A B f g i)). Qed.
Lemma lem7623219 (P : nat -> Prop) : (term68 P) = (term69 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7623220 {A B : Type'} (f : cart A B) (g : nat -> A) : (term70 A B f g) = (term71 A B f g).
Proof. exact (@lem7623219 (term57 A B f g)). Qed.
Lemma lem7623221 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term72 A B f g i) = (term56 A B f g i).
Proof. exact (eq_refl (term72 A B f g i)). Qed.
Lemma lem7623222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7623223 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term73 A B f g i) = (term62 A B f g i).
Proof. exact (MK_COMB (@lem7623222) (@lem7623221 A B f g i)). Qed.
Lemma lem7623224 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term73 A B f g i) = (term63 A B f g i).
Proof. exact (TRANS (@lem7623223 A B f g i) (@lem7623213 A B f g i)). Qed.
Lemma lem7623225 {A B : Type'} (f : cart A B) (g : nat -> A) : (term74 A B f g) = (term75 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623224 A B f g i)). Qed.
Lemma lem7623226 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623227 {A B : Type'} (f : cart A B) (g : nat -> A) : (term71 A B f g) = (term76 A B f g).
Proof. exact (MK_COMB (@lem7623226) (@lem7623225 A B f g)). Qed.
Lemma lem7623228 {A B : Type'} (f : cart A B) (g : nat -> A) : (term70 A B f g) = (term76 A B f g).
Proof. exact (TRANS (@lem7623220 A B f g) (@lem7623227 A B f g)). Qed.
Lemma lem7623229 {A B : Type'} (f : cart A B) (g : nat -> A) : (term57 A B f g) = (term77 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623218 A B f g i)). Qed.
Lemma lem7623230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623231 {A B : Type'} (f : cart A B) (g : nat -> A) : (term39 A B f g) = (term78 A B f g).
Proof. exact (MK_COMB (@lem7623230) (@lem7623229 A B f g)). Qed.
Lemma lem7623240 {B : Type'} (i : nat) : (term60 B i) = (term61 B i).
Proof. exact (@lem17045 (term27 i) (term26 B i)). Qed.
Lemma lem7623245 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : ((g i) = (@dollar A B f i)) = ((g i) = (@dollar A B f i)).
Proof. exact (eq_refl ((g i) = (@dollar A B f i))). Qed.
Lemma lem7623250 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term79 A B g f i) = (term80 A B g f i).
Proof. exact (@lem17362 (term9 B i) ((g i) = (@dollar A B f i))). Qed.
Lemma lem7623251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623252 {B : Type'} (i : nat) : (term64 B i) = (term65 B i).
Proof. exact (MK_COMB (@lem7623251) (@lem7623240 B i)). Qed.
Lemma lem7623253 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term81 A B g f i) = (term82 A B g f i).
Proof. exact (MK_COMB (@lem7623252 B i) (@lem7623245 A B g f i)). Qed.
Lemma lem7623254 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term34 A B g f i) = (term81 A B g f i).
Proof. exact (@lem17265 (term9 B i) ((g i) = (@dollar A B f i))). Qed.
Lemma lem7623255 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term34 A B g f i) = (term82 A B g f i).
Proof. exact (TRANS (@lem7623254 A B g f i) (@lem7623253 A B g f i)). Qed.
Lemma lem7623256 (P : nat -> Prop) : (term68 P) = (term69 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7623257 {A B : Type'} (g : nat -> A) (f : cart A B) : (term83 A B g f) = (term84 A B g f).
Proof. exact (@lem7623256 (term36 A B g f)). Qed.
Lemma lem7623258 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term85 A B g f i) = (term34 A B g f i).
Proof. exact (eq_refl (term85 A B g f i)). Qed.
Lemma lem7623259 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7623260 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term86 A B g f i) = (term79 A B g f i).
Proof. exact (MK_COMB (@lem7623259) (@lem7623258 A B g f i)). Qed.
Lemma lem7623261 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term86 A B g f i) = (term80 A B g f i).
Proof. exact (TRANS (@lem7623260 A B g f i) (@lem7623250 A B g f i)). Qed.
Lemma lem7623262 {A B : Type'} (g : nat -> A) (f : cart A B) : (term87 A B g f) = (term88 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623261 A B g f i)). Qed.
Lemma lem7623263 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623264 {A B : Type'} (g : nat -> A) (f : cart A B) : (term84 A B g f) = (term89 A B g f).
Proof. exact (MK_COMB (@lem7623263) (@lem7623262 A B g f)). Qed.
Lemma lem7623265 {A B : Type'} (g : nat -> A) (f : cart A B) : (term83 A B g f) = (term89 A B g f).
Proof. exact (TRANS (@lem7623257 A B g f) (@lem7623264 A B g f)). Qed.
Lemma lem7623266 {A B : Type'} (g : nat -> A) (f : cart A B) : (term36 A B g f) = (term90 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623255 A B g f i)). Qed.
Lemma lem7623267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623268 {A B : Type'} (g : nat -> A) (f : cart A B) : (term37 A B g f) = (term91 A B g f).
Proof. exact (MK_COMB (@lem7623267) (@lem7623266 A B g f)). Qed.
Lemma lem7623269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7623270 {A B : Type'} (f : cart A B) (g : nat -> A) : (term92 A B f g) = (term93 A B f g).
Proof. exact (MK_COMB (@lem7623269) (@lem7623228 A B f g)). Qed.
Lemma lem7623271 {A B : Type'} (g : nat -> A) (f : cart A B) : (term94 A B g f) = (term95 A B g f).
Proof. exact (MK_COMB (@lem7623270 A B f g) (@lem7623268 A B g f)). Qed.
Lemma lem7623272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7623273 {A B : Type'} (f : cart A B) (g : nat -> A) : (term96 A B f g) = (term97 A B f g).
Proof. exact (MK_COMB (@lem7623272) (@lem7623231 A B f g)). Qed.
Lemma lem7623274 {A B : Type'} (g : nat -> A) (f : cart A B) : (term98 A B g f) = (term99 A B g f).
Proof. exact (MK_COMB (@lem7623273 A B f g) (@lem7623265 A B g f)). Qed.
Lemma lem7623275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623276 {A B : Type'} (g : nat -> A) (f : cart A B) : (term100 A B g f) = (term101 A B g f).
Proof. exact (MK_COMB (@lem7623275) (@lem7623274 A B g f)). Qed.
Lemma lem7623277 {A B : Type'} (g : nat -> A) (f : cart A B) : (term102 A B g f) = (term103 A B g f).
Proof. exact (MK_COMB (@lem7623276 A B g f) (@lem7623271 A B g f)). Qed.
Lemma lem7623278 {A B : Type'} (g : nat -> A) (f : cart A B) : (term59 A B g f) = (term102 A B g f).
Proof. exact (@lem17646 (term39 A B f g) (term37 A B g f)). Qed.
Lemma lem7623279 {A B : Type'} (g : nat -> A) (f : cart A B) : (term59 A B g f) = (term103 A B g f).
Proof. exact (TRANS (@lem7623278 A B g f) (@lem7623277 A B g f)). Qed.
Lemma lem7623474 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7623475 (P : Prop) (Q : nat -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem7623474 nat P Q). Qed.
Lemma lem7623476 {A B : Type'} (g : nat -> A) (f : cart A B) : (term108 A B g f) = (term109 A B g f).
Proof. exact (@lem7623475 (term78 A B f g) (term88 A B g f)). Qed.
Lemma lem7623477 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term110 A B g f i) = (term80 A B g f i).
Proof. exact (eq_refl (term110 A B g f i)). Qed.
Lemma lem7623478 {A B : Type'} (g : nat -> A) (f : cart A B) : (term111 A B g f) = (term88 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623477 A B g f i)). Qed.
Lemma lem7623479 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623480 {A B : Type'} (g : nat -> A) (f : cart A B) : (term112 A B g f) = (term89 A B g f).
Proof. exact (MK_COMB (@lem7623479) (@lem7623478 A B g f)). Qed.
Lemma lem7623481 {A B : Type'} (f : cart A B) (g : nat -> A) : (term97 A B f g) = (term97 A B f g).
Proof. exact (eq_refl (term97 A B f g)). Qed.
Lemma lem7623482 {A B : Type'} (g : nat -> A) (f : cart A B) : (term108 A B g f) = (term99 A B g f).
Proof. exact (MK_COMB (@lem7623481 A B f g) (@lem7623480 A B g f)). Qed.
Lemma lem7623483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7623484 {A B : Type'} (g : nat -> A) (f : cart A B) : (term113 A B g f) = (term114 A B g f).
Proof. exact (MK_COMB (@lem7623483) (@lem7623482 A B g f)). Qed.
Lemma lem7623485 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term110 A B g f i) = (term80 A B g f i).
Proof. exact (eq_refl (term110 A B g f i)). Qed.
Lemma lem7623486 {A B : Type'} (f : cart A B) (g : nat -> A) : (term97 A B f g) = (term97 A B f g).
Proof. exact (eq_refl (term97 A B f g)). Qed.
Lemma lem7623487 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term115 A B g f i) = (term116 A B g f i).
Proof. exact (MK_COMB (@lem7623486 A B f g) (@lem7623485 A B g f i)). Qed.
Lemma lem7623488 {A B : Type'} (g : nat -> A) (f : cart A B) : (term117 A B g f) = (term118 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623487 A B g f i)). Qed.
Lemma lem7623489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623490 {A B : Type'} (g : nat -> A) (f : cart A B) : (term109 A B g f) = (term119 A B g f).
Proof. exact (MK_COMB (@lem7623489) (@lem7623488 A B g f)). Qed.
Lemma lem7623491 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term108 A B g f) = (term109 A B g f)) = ((term99 A B g f) = (term119 A B g f)).
Proof. exact (MK_COMB (@lem7623484 A B g f) (@lem7623490 A B g f)). Qed.
Lemma lem7623492 {A B : Type'} (g : nat -> A) (f : cart A B) : (term99 A B g f) = (term119 A B g f).
Proof. exact (EQ_MP (@lem7623491 A B g f) (@lem7623476 A B g f)). Qed.
Lemma lem7623493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623494 {A B : Type'} (g : nat -> A) (f : cart A B) : (term101 A B g f) = (term120 A B g f).
Proof. exact (MK_COMB (@lem7623493) (@lem7623492 A B g f)). Qed.
Lemma lem7623496 {A : Type'} (P : A -> Prop) (Q : Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7623497 (P : nat -> Prop) (Q : Prop) : (term123 P Q) = (term124 P Q).
Proof. exact (@lem7623496 nat P Q). Qed.
Lemma lem7623498 {A B : Type'} (g : nat -> A) (f : cart A B) : (term125 A B g f) = (term126 A B g f).
Proof. exact (@lem7623497 (term75 A B f g) (term91 A B g f)). Qed.
Lemma lem7623499 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term127 A B f g i) = (term63 A B f g i).
Proof. exact (eq_refl (term127 A B f g i)). Qed.
Lemma lem7623500 {A B : Type'} (f : cart A B) (g : nat -> A) : (term128 A B f g) = (term75 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623499 A B f g i)). Qed.
Lemma lem7623501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623502 {A B : Type'} (f : cart A B) (g : nat -> A) : (term129 A B f g) = (term76 A B f g).
Proof. exact (MK_COMB (@lem7623501) (@lem7623500 A B f g)). Qed.
Lemma lem7623503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7623504 {A B : Type'} (f : cart A B) (g : nat -> A) : (term130 A B f g) = (term93 A B f g).
Proof. exact (MK_COMB (@lem7623503) (@lem7623502 A B f g)). Qed.
Lemma lem7623505 {A B : Type'} (g : nat -> A) (f : cart A B) : (term91 A B g f) = (term91 A B g f).
Proof. exact (eq_refl (term91 A B g f)). Qed.
Lemma lem7623506 {A B : Type'} (g : nat -> A) (f : cart A B) : (term125 A B g f) = (term95 A B g f).
Proof. exact (MK_COMB (@lem7623504 A B f g) (@lem7623505 A B g f)). Qed.
Lemma lem7623507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7623508 {A B : Type'} (g : nat -> A) (f : cart A B) : (term131 A B g f) = (term132 A B g f).
Proof. exact (MK_COMB (@lem7623507) (@lem7623506 A B g f)). Qed.
Lemma lem7623509 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term127 A B f g i) = (term63 A B f g i).
Proof. exact (eq_refl (term127 A B f g i)). Qed.
Lemma lem7623510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7623511 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term133 A B f g i) = (term134 A B f g i).
Proof. exact (MK_COMB (@lem7623510) (@lem7623509 A B f g i)). Qed.
Lemma lem7623512 {A B : Type'} (g : nat -> A) (f : cart A B) : (term91 A B g f) = (term91 A B g f).
Proof. exact (eq_refl (term91 A B g f)). Qed.
Lemma lem7623513 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term135 A B i g f) = (term136 A B i g f).
Proof. exact (MK_COMB (@lem7623511 A B f g i) (@lem7623512 A B g f)). Qed.
Lemma lem7623514 {A B : Type'} (g : nat -> A) (f : cart A B) : (term137 A B g f) = (term138 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623513 A B i g f)). Qed.
Lemma lem7623515 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623516 {A B : Type'} (g : nat -> A) (f : cart A B) : (term126 A B g f) = (term139 A B g f).
Proof. exact (MK_COMB (@lem7623515) (@lem7623514 A B g f)). Qed.
Lemma lem7623517 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term125 A B g f) = (term126 A B g f)) = ((term95 A B g f) = (term139 A B g f)).
Proof. exact (MK_COMB (@lem7623508 A B g f) (@lem7623516 A B g f)). Qed.
Lemma lem7623518 {A B : Type'} (g : nat -> A) (f : cart A B) : (term95 A B g f) = (term139 A B g f).
Proof. exact (EQ_MP (@lem7623517 A B g f) (@lem7623498 A B g f)). Qed.
Lemma lem7623519 {A B : Type'} (g : nat -> A) (f : cart A B) : (term103 A B g f) = (term140 A B g f).
Proof. exact (MK_COMB (@lem7623494 A B g f) (@lem7623518 A B g f)). Qed.
Lemma lem7623521 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7623522 (P : nat -> Prop) (Q : nat -> Prop) : (term143 P Q) = (term144 P Q).
Proof. exact (@lem7623521 nat P Q). Qed.
Lemma lem7623523 {A B : Type'} (g : nat -> A) (f : cart A B) : (term145 A B g f) = (term146 A B g f).
Proof. exact (@lem7623522 (term118 A B g f) (term138 A B g f)). Qed.
Lemma lem7623524 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term147 A B g f i) = (term116 A B g f i).
Proof. exact (eq_refl (term147 A B g f i)). Qed.
Lemma lem7623525 {A B : Type'} (g : nat -> A) (f : cart A B) : (term148 A B g f) = (term118 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623524 A B g f i)). Qed.
Lemma lem7623526 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623527 {A B : Type'} (g : nat -> A) (f : cart A B) : (term149 A B g f) = (term119 A B g f).
Proof. exact (MK_COMB (@lem7623526) (@lem7623525 A B g f)). Qed.
Lemma lem7623528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623529 {A B : Type'} (g : nat -> A) (f : cart A B) : (term150 A B g f) = (term120 A B g f).
Proof. exact (MK_COMB (@lem7623528) (@lem7623527 A B g f)). Qed.
Lemma lem7623530 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term151 A B g f i) = (term136 A B i g f).
Proof. exact (eq_refl (term151 A B g f i)). Qed.
Lemma lem7623531 {A B : Type'} (g : nat -> A) (f : cart A B) : (term152 A B g f) = (term138 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623530 A B i g f)). Qed.
Lemma lem7623532 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623533 {A B : Type'} (g : nat -> A) (f : cart A B) : (term153 A B g f) = (term139 A B g f).
Proof. exact (MK_COMB (@lem7623532) (@lem7623531 A B g f)). Qed.
Lemma lem7623534 {A B : Type'} (g : nat -> A) (f : cart A B) : (term145 A B g f) = (term140 A B g f).
Proof. exact (MK_COMB (@lem7623529 A B g f) (@lem7623533 A B g f)). Qed.
Lemma lem7623535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7623536 {A B : Type'} (g : nat -> A) (f : cart A B) : (term154 A B g f) = (term155 A B g f).
Proof. exact (MK_COMB (@lem7623535) (@lem7623534 A B g f)). Qed.
Lemma lem7623537 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term147 A B g f i) = (term116 A B g f i).
Proof. exact (eq_refl (term147 A B g f i)). Qed.
Lemma lem7623538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623539 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term156 A B g f i) = (term157 A B g f i).
Proof. exact (MK_COMB (@lem7623538) (@lem7623537 A B g f i)). Qed.
Lemma lem7623540 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term151 A B g f i) = (term136 A B i g f).
Proof. exact (eq_refl (term151 A B g f i)). Qed.
Lemma lem7623541 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term158 A B g f i) = (term159 A B i g f).
Proof. exact (MK_COMB (@lem7623539 A B g f i) (@lem7623540 A B i g f)). Qed.
Lemma lem7623542 {A B : Type'} (g : nat -> A) (f : cart A B) : (term160 A B g f) = (term161 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623541 A B i g f)). Qed.
Lemma lem7623543 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7623544 {A B : Type'} (g : nat -> A) (f : cart A B) : (term146 A B g f) = (term162 A B g f).
Proof. exact (MK_COMB (@lem7623543) (@lem7623542 A B g f)). Qed.
Lemma lem7623545 {A B : Type'} (g : nat -> A) (f : cart A B) : ((term145 A B g f) = (term146 A B g f)) = ((term140 A B g f) = (term162 A B g f)).
Proof. exact (MK_COMB (@lem7623536 A B g f) (@lem7623544 A B g f)). Qed.
Lemma lem7623546 {A B : Type'} (g : nat -> A) (f : cart A B) : (term140 A B g f) = (term162 A B g f).
Proof. exact (EQ_MP (@lem7623545 A B g f) (@lem7623523 A B g f)). Qed.
Lemma lem7623548 {A B : Type'} (g : nat -> A) (f : cart A B) : (term103 A B g f) = (term162 A B g f).
Proof. exact (TRANS (@lem7623519 A B g f) (@lem7623546 A B g f)). Qed.
Lemma lem7623549 {A B : Type'} (g : nat -> A) (f : cart A B) : (term59 A B g f) = (term162 A B g f).
Proof. exact (TRANS (@lem7623279 A B g f) (@lem7623548 A B g f)). Qed.
Lemma lem7623550 {A B : Type'} (g : nat -> A) (f : cart A B) (h1 : term59 A B g f) : term162 A B g f.
Proof. exact (EQ_MP (@lem7623549 A B g f) (@lem7623194 A B g f h1)). Qed.
Lemma lem7623551 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term159 A B i g f) : term159 A B i g f.
Proof. exact (h1). Qed.
Lemma lem7623588 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term82 A B g f i) = (term82 A B g f i).
Proof. exact (eq_refl (term82 A B g f i)). Qed.
Lemma lem7623589 {A B : Type'} (g : nat -> A) (f : cart A B) : (term90 A B g f) = (term90 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623588 A B g f i)). Qed.
Lemma lem7623590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623591 {A B : Type'} (g : nat -> A) (f : cart A B) : (term91 A B g f) = (term91 A B g f).
Proof. exact (MK_COMB (@lem7623590) (@lem7623589 A B g f)). Qed.
Lemma lem7623628 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term134 A B f g i) = (term134 A B f g i).
Proof. exact (eq_refl (term134 A B f g i)). Qed.
Lemma lem7623629 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term136 A B i g f) = (term136 A B i g f).
Proof. exact (MK_COMB (@lem7623628 A B f g i) (@lem7623591 A B g f)). Qed.
Lemma lem7623664 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term80 A B g f i) = (term80 A B g f i).
Proof. exact (eq_refl (term80 A B g f i)). Qed.
Lemma lem7623701 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term67 A B f g i) = (term67 A B f g i).
Proof. exact (eq_refl (term67 A B f g i)). Qed.
Lemma lem7623702 {A B : Type'} (f : cart A B) (g : nat -> A) : (term77 A B f g) = (term77 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623701 A B f g i)). Qed.
Lemma lem7623703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623704 {A B : Type'} (f : cart A B) (g : nat -> A) : (term78 A B f g) = (term78 A B f g).
Proof. exact (MK_COMB (@lem7623703) (@lem7623702 A B f g)). Qed.
Lemma lem7623705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7623706 {A B : Type'} (f : cart A B) (g : nat -> A) : (term97 A B f g) = (term97 A B f g).
Proof. exact (MK_COMB (@lem7623705) (@lem7623704 A B f g)). Qed.
Lemma lem7623707 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term116 A B g f i) = (term116 A B g f i).
Proof. exact (MK_COMB (@lem7623706 A B f g) (@lem7623664 A B g f i)). Qed.
Lemma lem7623708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7623709 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term157 A B g f i) = (term157 A B g f i).
Proof. exact (MK_COMB (@lem7623708) (@lem7623707 A B g f i)). Qed.
Lemma lem7623710 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) : (term159 A B i g f) = (term159 A B i g f).
Proof. exact (MK_COMB (@lem7623709 A B g f i) (@lem7623629 A B i g f)). Qed.
Lemma lem7623711 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term159 A B i g f) : term159 A B i g f.
Proof. exact (EQ_MP (@lem7623710 A B i g f) (@lem7623551 A B i g f h1)). Qed.
Lemma lem7623712 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term116 A B g f i.
Proof. exact (h1). Qed.
Lemma lem7623713 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term136 A B i g f.
Proof. exact (h1). Qed.
Lemma lem7623714 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term80 A B g f i.
Proof. exact (proj2 (@lem7623712 A B g f i h1)). Qed.
Lemma lem7623715 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term78 A B f g.
Proof. exact (proj1 (@lem7623712 A B g f i h1)). Qed.
Lemma lem7623717 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term9 B i.
Proof. exact (proj1 (@lem7623714 A B g f i h1)). Qed.
Lemma lem7623720 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term91 A B g f.
Proof. exact (proj2 (@lem7623713 A B i g f h1)). Qed.
Lemma lem7623721 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term63 A B f g i.
Proof. exact (proj1 (@lem7623713 A B i g f h1)). Qed.
Lemma lem7623723 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term9 B i.
Proof. exact (proj1 (@lem7623721 A B i g f h1)). Qed.
Lemma lem7623739 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term67 A B f g i) = (term67 A B f g i).
Proof. exact (eq_refl (term67 A B f g i)). Qed.
Lemma lem7623740 {A B : Type'} (f : cart A B) (g : nat -> A) : (term77 A B f g) = (term77 A B f g).
Proof. exact (fun_ext (fun i : nat => @lem7623739 A B f g i)). Qed.
Lemma lem7623741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623743 {A B : Type'} (f : cart A B) (g : nat -> A) : (term78 A B f g) = (term78 A B f g).
Proof. exact (MK_COMB (@lem7623741) (@lem7623740 A B f g)). Qed.
Lemma lem7623744 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term78 A B f g.
Proof. exact (EQ_MP (@lem7623743 A B f g) (@lem7623715 A B g f i h1)). Qed.
Lemma lem7623770 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term82 A B g f i) = (term82 A B g f i).
Proof. exact (eq_refl (term82 A B g f i)). Qed.
Lemma lem7623771 {A B : Type'} (g : nat -> A) (f : cart A B) : (term90 A B g f) = (term90 A B g f).
Proof. exact (fun_ext (fun i : nat => @lem7623770 A B g f i)). Qed.
Lemma lem7623772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7623774 {A B : Type'} (g : nat -> A) (f : cart A B) : (term91 A B g f) = (term91 A B g f).
Proof. exact (MK_COMB (@lem7623772) (@lem7623771 A B g f)). Qed.
Lemma lem7623775 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term91 A B g f.
Proof. exact (EQ_MP (@lem7623774 A B g f) (@lem7623720 A B i g f h1)). Qed.
Lemma lem7623788 {A B : Type'} (_98242 : nat) (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term163 A B f g _98242.
Proof. exact (@lem7623744 A B g f i h1 _98242). Qed.
Lemma lem7623789 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term163 A B f g _98242) = (term67 A B f g _98242).
Proof. exact (eq_refl (term163 A B f g _98242)). Qed.
Lemma lem7623790 {A B : Type'} (_98242 : nat) (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term67 A B f g _98242.
Proof. exact (EQ_MP (@lem7623789 A B f g _98242) (@lem7623788 A B _98242 g f i h1)). Qed.
Lemma lem7623791 {A B : Type'} (_98243 : nat) (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term164 A B g f _98243.
Proof. exact (@lem7623775 A B i g f h1 _98243). Qed.
Lemma lem7623792 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term164 A B g f _98243) = (term82 A B g f _98243).
Proof. exact (eq_refl (term164 A B g f _98243)). Qed.
Lemma lem7623793 {A B : Type'} (_98243 : nat) (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term82 A B g f _98243.
Proof. exact (EQ_MP (@lem7623792 A B g f _98243) (@lem7623791 A B _98243 i g f h1)). Qed.
Lemma lem7623804 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term67 A B f g _98242) = (term165 A B f g _98242).
Proof. exact (@lem7622324 (term166 _98242) (term167 B _98242) ((@dollar A B f _98242) = (g _98242))). Qed.
Lemma lem7623805 {A B : Type'} (_98242 : nat) (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term165 A B f g _98242.
Proof. exact (EQ_MP (@lem7623804 A B f g _98242) (@lem7623790 A B _98242 g f i h1)). Qed.
Lemma lem7623807 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term168 A B g f i.
Proof. exact (proj2 (@lem7623714 A B g f i h1)). Qed.
Lemma lem7623822 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term82 A B g f _98243) = (term169 A B g f _98243).
Proof. exact (@lem7622324 (term166 _98243) (term167 B _98243) ((g _98243) = (@dollar A B f _98243))). Qed.
Lemma lem7623823 {A B : Type'} (_98243 : nat) (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term169 A B g f _98243.
Proof. exact (EQ_MP (@lem7623822 A B g f _98243) (@lem7623793 A B _98243 i g f h1)). Qed.
Lemma lem7623825 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term170 A B f g i.
Proof. exact (proj2 (@lem7623721 A B i g f h1)). Qed.
Lemma lem7623897 {A : Type'} (x : A) (y : A) (z : A) : term171 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem7623905 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term27 i.
Proof. exact (proj1 (@lem7623717 A B g f i h1)). Qed.
Lemma lem7623906 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term172 i.
Proof. exact (fun h0 : term166 i => @lem7623905 A B g f i h1). Qed.
Lemma lem7623908 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7623909 (i : nat) : (term172 i) = (term27 i).
Proof. exact (@lem7623908 (term27 i)). Qed.
Lemma lem7623910 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term27 i.
Proof. exact (EQ_MP (@lem7623909 i) (@lem7623906 A B g f i h1)). Qed.
Lemma lem7623912 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term26 B i.
Proof. exact (proj2 (@lem7623717 A B g f i h1)). Qed.
Lemma lem7623913 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term174 B i.
Proof. exact (fun h0 : term167 B i => @lem7623912 A B g f i h1). Qed.
Lemma lem7623915 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7623916 {B : Type'} (i : nat) : (term174 B i) = (term26 B i).
Proof. exact (@lem7623915 (term26 B i)). Qed.
Lemma lem7623917 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term26 B i.
Proof. exact (EQ_MP (@lem7623916 B i) (@lem7623913 A B g f i h1)). Qed.
Lemma lem7623923 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7623924 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term165 A B f g _98242) = (term175 A B f g _98242).
Proof. exact (@lem7623923 (term167 B _98242) (term166 _98242) ((@dollar A B f _98242) = (g _98242))). Qed.
Lemma lem7623938 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7623939 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term176 A B f g _98242) = (term177 A B f g _98242).
Proof. exact (@lem7623938 ((@dollar A B f _98242) = (g _98242)) (term166 _98242)). Qed.
Lemma lem7623947 {B : Type'} (_98242 : nat) : (term178 B _98242) = (term178 B _98242).
Proof. exact (eq_refl (term178 B _98242)). Qed.
Lemma lem7623948 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term175 A B f g _98242) = (term179 A B f g _98242).
Proof. exact (MK_COMB (@lem7623947 B _98242) (@lem7623939 A B f g _98242)). Qed.
Lemma lem7623952 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7623953 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term179 A B f g _98242) = (term180 A B f g _98242).
Proof. exact (@lem7623952 ((@dollar A B f _98242) = (g _98242)) (term167 B _98242) (term166 _98242)). Qed.
Lemma lem7623971 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term175 A B f g _98242) = (term180 A B f g _98242).
Proof. exact (TRANS (@lem7623948 A B f g _98242) (@lem7623953 A B f g _98242)). Qed.
Lemma lem7623972 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term165 A B f g _98242) = (term180 A B f g _98242).
Proof. exact (TRANS (@lem7623924 A B f g _98242) (@lem7623971 A B f g _98242)). Qed.
Lemma lem7623973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7623974 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term181 A B f g _98242) = (term182 A B f g _98242).
Proof. exact (MK_COMB (@lem7623973) (@lem7623972 A B f g _98242)). Qed.
Lemma lem7623990 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7623991 {B : Type'} (_98242 : nat) : (term61 B _98242) = (term183 B _98242).
Proof. exact (@lem7623990 (term167 B _98242) (term166 _98242)). Qed.
Lemma lem7623997 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term184 A B f g _98242) = (term184 A B f g _98242).
Proof. exact (eq_refl (term184 A B f g _98242)). Qed.
Lemma lem7623998 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term185 A B f g _98242) = (term180 A B f g _98242).
Proof. exact (MK_COMB (@lem7623997 A B f g _98242) (@lem7623991 B _98242)). Qed.
Lemma lem7624009 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : ((term165 A B f g _98242) = (term185 A B f g _98242)) = ((term180 A B f g _98242) = (term180 A B f g _98242)).
Proof. exact (MK_COMB (@lem7623974 A B f g _98242) (@lem7623998 A B f g _98242)). Qed.
Lemma lem7624011 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7624012 (x : Prop) : (x = x) = True.
Proof. exact (@lem7624011 Prop x). Qed.
Lemma lem7624013 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : ((term180 A B f g _98242) = (term180 A B f g _98242)) = True.
Proof. exact (@lem7624012 (term180 A B f g _98242)). Qed.
Lemma lem7624014 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : ((term165 A B f g _98242) = (term185 A B f g _98242)) = True.
Proof. exact (TRANS (@lem7624009 A B f g _98242) (@lem7624013 A B f g _98242)). Qed.
Lemma lem7624015 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : True = ((term165 A B f g _98242) = (term185 A B f g _98242)).
Proof. exact (SYM (@lem7624014 A B f g _98242)). Qed.
Lemma lem7624016 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term165 A B f g _98242) = (term185 A B f g _98242).
Proof. exact (EQ_MP (@lem7624015 A B f g _98242) (@lem0)). Qed.
Lemma lem7624017 {A B : Type'} (_98242 : nat) (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term185 A B f g _98242.
Proof. exact (EQ_MP (@lem7624016 A B f g _98242) (@lem7623805 A B _98242 g f i h1)). Qed.
Lemma lem7624019 (b : Prop) (a : Prop) : (a \/ b) = (term186 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7624020 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term185 A B f g _98242) = (term187 A B f g _98242).
Proof. exact (@lem7624019 (term61 B _98242) ((@dollar A B f _98242) = (g _98242))). Qed.
Lemma lem7624022 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7624023 {B : Type'} (_98242 : nat) : (term190 B _98242) = (term191 B _98242).
Proof. exact (@lem7624022 (term166 _98242) (term167 B _98242)). Qed.
Lemma lem7624025 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624026 (_98242 : nat) : (term192 _98242) = (term27 _98242).
Proof. exact (@lem7624025 (term27 _98242)). Qed.
Lemma lem7624027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7624028 (_98242 : nat) : (term193 _98242) = (term28 _98242).
Proof. exact (MK_COMB (@lem7624027) (@lem7624026 _98242)). Qed.
Lemma lem7624030 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624031 {B : Type'} (_98242 : nat) : (term194 B _98242) = (term26 B _98242).
Proof. exact (@lem7624030 (term26 B _98242)). Qed.
Lemma lem7624032 {B : Type'} (_98242 : nat) : (term191 B _98242) = (term9 B _98242).
Proof. exact (MK_COMB (@lem7624028 _98242) (@lem7624031 B _98242)). Qed.
Lemma lem7624033 {B : Type'} (_98242 : nat) : (term190 B _98242) = (term9 B _98242).
Proof. exact (TRANS (@lem7624023 B _98242) (@lem7624032 B _98242)). Qed.
Lemma lem7624034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7624035 {B : Type'} (_98242 : nat) : (term195 B _98242) = (term196 B _98242).
Proof. exact (MK_COMB (@lem7624034) (@lem7624033 B _98242)). Qed.
Lemma lem7624036 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : ((@dollar A B f _98242) = (g _98242)) = ((@dollar A B f _98242) = (g _98242)).
Proof. exact (eq_refl ((@dollar A B f _98242) = (g _98242))). Qed.
Lemma lem7624037 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term187 A B f g _98242) = (term56 A B f g _98242).
Proof. exact (MK_COMB (@lem7624035 B _98242) (@lem7624036 A B f g _98242)). Qed.
Lemma lem7624038 {A B : Type'} (f : cart A B) (g : nat -> A) (_98242 : nat) : (term185 A B f g _98242) = (term56 A B f g _98242).
Proof. exact (TRANS (@lem7624020 A B f g _98242) (@lem7624037 A B f g _98242)). Qed.
Lemma lem7624040 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term9 B i.
Proof. exact (conj (@lem7623910 A B g f i h1) (@lem7623917 A B g f i h1)). Qed.
Lemma lem7624042 {A B : Type'} (_98242 : nat) (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term56 A B f g _98242.
Proof. exact (EQ_MP (@lem7624038 A B f g _98242) (@lem7624017 A B _98242 g f i h1)). Qed.
Lemma lem7624043 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term56 A B f g i.
Proof. exact (@lem7624042 A B i g f i h1). Qed.
Lemma lem7624046 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : (@dollar A B f i) = (g i).
Proof. exact (@lem7624043 A B g f i h1 (@lem7624040 A B g f i h1)). Qed.
Lemma lem7624047 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term197 A B f g i.
Proof. exact (fun h0 : term170 A B f g i => @lem7624046 A B g f i h1). Qed.
Lemma lem7624049 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624050 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term197 A B f g i) = ((@dollar A B f i) = (g i)).
Proof. exact (@lem7624049 ((@dollar A B f i) = (g i))). Qed.
Lemma lem7624051 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : (@dollar A B f i) = (g i).
Proof. exact (EQ_MP (@lem7624050 A B f g i) (@lem7624047 A B g f i h1)). Qed.
Lemma lem7624053 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7624054 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7624053 A x). Qed.
Lemma lem7624055 {A B : Type'} (f : cart A B) (i : nat) : (@dollar A B f i) = (@dollar A B f i).
Proof. exact (@lem7624054 A (@dollar A B f i)). Qed.
Lemma lem7624056 {A B : Type'} (f : cart A B) (i : nat) : term198 A B f i.
Proof. exact (fun h0 : term199 A B f i => @lem7624055 A B f i). Qed.
Lemma lem7624058 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624059 {A B : Type'} (f : cart A B) (i : nat) : (term198 A B f i) = ((@dollar A B f i) = (@dollar A B f i)).
Proof. exact (@lem7624058 ((@dollar A B f i) = (@dollar A B f i))). Qed.
Lemma lem7624060 {A B : Type'} (f : cart A B) (i : nat) : (@dollar A B f i) = (@dollar A B f i).
Proof. exact (EQ_MP (@lem7624059 A B f i) (@lem7624056 A B f i)). Qed.
Lemma lem7624078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7624079 {A : Type'} (y : A) (x : A) (z : A) : (term200 A x y z) = (term201 A y x z).
Proof. exact (@lem7624078 (y = z) (term202 A x z)). Qed.
Lemma lem7624089 {A : Type'} (x : A) (y : A) : (term203 A x y) = (term203 A x y).
Proof. exact (eq_refl (term203 A x y)). Qed.
Lemma lem7624090 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term204 A y x z).
Proof. exact (MK_COMB (@lem7624089 A x y) (@lem7624079 A y x z)). Qed.
Lemma lem7624094 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7624095 {A : Type'} (y : A) (x : A) (z : A) : (term204 A y x z) = (term205 A y x z).
Proof. exact (@lem7624094 (y = z) (term202 A x y) (term202 A x z)). Qed.
Lemma lem7624117 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term205 A y x z).
Proof. exact (TRANS (@lem7624090 A y x z) (@lem7624095 A y x z)). Qed.
Lemma lem7624118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7624119 {A : Type'} (y : A) (x : A) (z : A) : (term206 A x y z) = (term207 A y x z).
Proof. exact (MK_COMB (@lem7624118) (@lem7624117 A y x z)). Qed.
Lemma lem7624141 {A : Type'} (y : A) (x : A) (z : A) : (term205 A y x z) = (term205 A y x z).
Proof. exact (eq_refl (term205 A y x z)). Qed.
Lemma lem7624142 {A : Type'} (y : A) (x : A) (z : A) : ((term171 A x y z) = (term205 A y x z)) = ((term205 A y x z) = (term205 A y x z)).
Proof. exact (MK_COMB (@lem7624119 A y x z) (@lem7624141 A y x z)). Qed.
Lemma lem7624144 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7624145 (x : Prop) : (x = x) = True.
Proof. exact (@lem7624144 Prop x). Qed.
Lemma lem7624146 {A : Type'} (y : A) (x : A) (z : A) : ((term205 A y x z) = (term205 A y x z)) = True.
Proof. exact (@lem7624145 (term205 A y x z)). Qed.
Lemma lem7624147 {A : Type'} (y : A) (x : A) (z : A) : ((term171 A x y z) = (term205 A y x z)) = True.
Proof. exact (TRANS (@lem7624142 A y x z) (@lem7624146 A y x z)). Qed.
Lemma lem7624148 {A : Type'} (y : A) (x : A) (z : A) : True = ((term171 A x y z) = (term205 A y x z)).
Proof. exact (SYM (@lem7624147 A y x z)). Qed.
Lemma lem7624149 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term205 A y x z).
Proof. exact (EQ_MP (@lem7624148 A y x z) (@lem0)). Qed.
Lemma lem7624150 {A : Type'} (y : A) (x : A) (z : A) : term205 A y x z.
Proof. exact (EQ_MP (@lem7624149 A y x z) (@lem7623897 A x y z)). Qed.
Lemma lem7624152 (b : Prop) (a : Prop) : (a \/ b) = (term186 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7624153 {A : Type'} (x : A) (y : A) (z : A) : (term205 A y x z) = (term208 A x y z).
Proof. exact (@lem7624152 (term209 A y x z) (y = z)). Qed.
Lemma lem7624155 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7624156 {A : Type'} (y : A) (x : A) (z : A) : (term210 A y x z) = (term211 A y x z).
Proof. exact (@lem7624155 (term202 A x y) (term202 A x z)). Qed.
Lemma lem7624158 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624159 {A : Type'} (x : A) (y : A) : (term212 A x y) = (x = y).
Proof. exact (@lem7624158 (x = y)). Qed.
Lemma lem7624160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7624161 {A : Type'} (x : A) (y : A) : (term213 A x y) = (term214 A x y).
Proof. exact (MK_COMB (@lem7624160) (@lem7624159 A x y)). Qed.
Lemma lem7624163 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624164 {A : Type'} (x : A) (z : A) : (term212 A x z) = (x = z).
Proof. exact (@lem7624163 (x = z)). Qed.
Lemma lem7624165 {A : Type'} (y : A) (x : A) (z : A) : (term211 A y x z) = (term215 A y x z).
Proof. exact (MK_COMB (@lem7624161 A x y) (@lem7624164 A x z)). Qed.
Lemma lem7624166 {A : Type'} (y : A) (x : A) (z : A) : (term210 A y x z) = (term215 A y x z).
Proof. exact (TRANS (@lem7624156 A y x z) (@lem7624165 A y x z)). Qed.
Lemma lem7624167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7624168 {A : Type'} (y : A) (x : A) (z : A) : (term216 A y x z) = (term217 A y x z).
Proof. exact (MK_COMB (@lem7624167) (@lem7624166 A y x z)). Qed.
Lemma lem7624169 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7624170 {A : Type'} (x : A) (y : A) (z : A) : (term208 A x y z) = (term218 A x y z).
Proof. exact (MK_COMB (@lem7624168 A y x z) (@lem7624169 A y z)). Qed.
Lemma lem7624171 {A : Type'} (x : A) (y : A) (z : A) : (term205 A y x z) = (term218 A x y z).
Proof. exact (TRANS (@lem7624153 A x y z) (@lem7624170 A x y z)). Qed.
Lemma lem7624173 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term219 A B g f i.
Proof. exact (conj (@lem7624051 A B g f i h1) (@lem7624060 A B f i)). Qed.
Lemma lem7624175 {A : Type'} (x : A) (y : A) (z : A) : term218 A x y z.
Proof. exact (EQ_MP (@lem7624171 A x y z) (@lem7624150 A y x z)). Qed.
Lemma lem7624176 {A : Type'} (x : A) (y : A) (z : A) : term218 A x y z.
Proof. exact (@lem7624175 A x y z). Qed.
Lemma lem7624177 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : term220 A B g f i.
Proof. exact (@lem7624176 A (@dollar A B f i) (g i) (@dollar A B f i)). Qed.
Lemma lem7624180 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : (g i) = (@dollar A B f i).
Proof. exact (@lem7624177 A B g f i (@lem7624173 A B g f i h1)). Qed.
Lemma lem7624181 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term221 A B g f i.
Proof. exact (fun h0 : term168 A B g f i => @lem7624180 A B g f i h1). Qed.
Lemma lem7624183 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624184 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term221 A B g f i) = ((g i) = (@dollar A B f i)).
Proof. exact (@lem7624183 ((g i) = (@dollar A B f i))). Qed.
Lemma lem7624185 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : (g i) = (@dollar A B f i).
Proof. exact (EQ_MP (@lem7624184 A B g f i) (@lem7624181 A B g f i h1)). Qed.
Lemma lem7624188 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7624190 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term168 A B g f i) = (term222 A B g f i).
Proof. exact (@lem7624188 ((g i) = (@dollar A B f i))). Qed.
Lemma lem7624193 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term222 A B g f i.
Proof. exact (EQ_MP (@lem7624190 A B g f i) (@lem7623807 A B g f i h1)). Qed.
Lemma lem7624196 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : False.
Proof. exact (@lem7624193 A B g f i h1 (@lem7624185 A B g f i h1)). Qed.
Lemma lem7624197 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : term223.
Proof. exact (fun h0 : ~ False => @lem7624196 A B g f i h1). Qed.
Lemma lem7624199 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624200 : term223 = False.
Proof. exact (@lem7624199 False). Qed.
Lemma lem7624201 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) (h1 : term116 A B g f i) : False.
Proof. exact (EQ_MP (@lem7624200) (@lem7624197 A B g f i h1)). Qed.
Lemma lem7624269 {A : Type'} (x : A) (y : A) (z : A) : term171 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem7624277 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term27 i.
Proof. exact (proj1 (@lem7623723 A B i g f h1)). Qed.
Lemma lem7624278 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term172 i.
Proof. exact (fun h0 : term166 i => @lem7624277 A B i g f h1). Qed.
Lemma lem7624280 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624281 (i : nat) : (term172 i) = (term27 i).
Proof. exact (@lem7624280 (term27 i)). Qed.
Lemma lem7624282 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term27 i.
Proof. exact (EQ_MP (@lem7624281 i) (@lem7624278 A B i g f h1)). Qed.
Lemma lem7624284 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term26 B i.
Proof. exact (proj2 (@lem7623723 A B i g f h1)). Qed.
Lemma lem7624285 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term174 B i.
Proof. exact (fun h0 : term167 B i => @lem7624284 A B i g f h1). Qed.
Lemma lem7624287 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624288 {B : Type'} (i : nat) : (term174 B i) = (term26 B i).
Proof. exact (@lem7624287 (term26 B i)). Qed.
Lemma lem7624289 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term26 B i.
Proof. exact (EQ_MP (@lem7624288 B i) (@lem7624285 A B i g f h1)). Qed.
Lemma lem7624295 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7624296 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term169 A B g f _98243) = (term224 A B g f _98243).
Proof. exact (@lem7624295 (term167 B _98243) (term166 _98243) ((g _98243) = (@dollar A B f _98243))). Qed.
Lemma lem7624310 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7624311 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term225 A B g f _98243) = (term226 A B g f _98243).
Proof. exact (@lem7624310 ((g _98243) = (@dollar A B f _98243)) (term166 _98243)). Qed.
Lemma lem7624319 {B : Type'} (_98243 : nat) : (term178 B _98243) = (term178 B _98243).
Proof. exact (eq_refl (term178 B _98243)). Qed.
Lemma lem7624320 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term224 A B g f _98243) = (term227 A B g f _98243).
Proof. exact (MK_COMB (@lem7624319 B _98243) (@lem7624311 A B g f _98243)). Qed.
Lemma lem7624324 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7624325 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term227 A B g f _98243) = (term228 A B g f _98243).
Proof. exact (@lem7624324 ((g _98243) = (@dollar A B f _98243)) (term167 B _98243) (term166 _98243)). Qed.
Lemma lem7624343 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term224 A B g f _98243) = (term228 A B g f _98243).
Proof. exact (TRANS (@lem7624320 A B g f _98243) (@lem7624325 A B g f _98243)). Qed.
Lemma lem7624344 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term169 A B g f _98243) = (term228 A B g f _98243).
Proof. exact (TRANS (@lem7624296 A B g f _98243) (@lem7624343 A B g f _98243)). Qed.
Lemma lem7624345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7624346 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term229 A B g f _98243) = (term230 A B g f _98243).
Proof. exact (MK_COMB (@lem7624345) (@lem7624344 A B g f _98243)). Qed.
Lemma lem7624362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7624363 {B : Type'} (_98243 : nat) : (term61 B _98243) = (term183 B _98243).
Proof. exact (@lem7624362 (term167 B _98243) (term166 _98243)). Qed.
Lemma lem7624369 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term231 A B g f _98243) = (term231 A B g f _98243).
Proof. exact (eq_refl (term231 A B g f _98243)). Qed.
Lemma lem7624370 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term232 A B g f _98243) = (term228 A B g f _98243).
Proof. exact (MK_COMB (@lem7624369 A B g f _98243) (@lem7624363 B _98243)). Qed.
Lemma lem7624381 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : ((term169 A B g f _98243) = (term232 A B g f _98243)) = ((term228 A B g f _98243) = (term228 A B g f _98243)).
Proof. exact (MK_COMB (@lem7624346 A B g f _98243) (@lem7624370 A B g f _98243)). Qed.
Lemma lem7624383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7624384 (x : Prop) : (x = x) = True.
Proof. exact (@lem7624383 Prop x). Qed.
Lemma lem7624385 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : ((term228 A B g f _98243) = (term228 A B g f _98243)) = True.
Proof. exact (@lem7624384 (term228 A B g f _98243)). Qed.
Lemma lem7624386 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : ((term169 A B g f _98243) = (term232 A B g f _98243)) = True.
Proof. exact (TRANS (@lem7624381 A B g f _98243) (@lem7624385 A B g f _98243)). Qed.
Lemma lem7624387 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : True = ((term169 A B g f _98243) = (term232 A B g f _98243)).
Proof. exact (SYM (@lem7624386 A B g f _98243)). Qed.
Lemma lem7624388 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term169 A B g f _98243) = (term232 A B g f _98243).
Proof. exact (EQ_MP (@lem7624387 A B g f _98243) (@lem0)). Qed.
Lemma lem7624389 {A B : Type'} (_98243 : nat) (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term232 A B g f _98243.
Proof. exact (EQ_MP (@lem7624388 A B g f _98243) (@lem7623823 A B _98243 i g f h1)). Qed.
Lemma lem7624391 (b : Prop) (a : Prop) : (a \/ b) = (term186 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7624392 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term232 A B g f _98243) = (term233 A B g f _98243).
Proof. exact (@lem7624391 (term61 B _98243) ((g _98243) = (@dollar A B f _98243))). Qed.
Lemma lem7624394 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7624395 {B : Type'} (_98243 : nat) : (term190 B _98243) = (term191 B _98243).
Proof. exact (@lem7624394 (term166 _98243) (term167 B _98243)). Qed.
Lemma lem7624397 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624398 (_98243 : nat) : (term192 _98243) = (term27 _98243).
Proof. exact (@lem7624397 (term27 _98243)). Qed.
Lemma lem7624399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7624400 (_98243 : nat) : (term193 _98243) = (term28 _98243).
Proof. exact (MK_COMB (@lem7624399) (@lem7624398 _98243)). Qed.
Lemma lem7624402 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624403 {B : Type'} (_98243 : nat) : (term194 B _98243) = (term26 B _98243).
Proof. exact (@lem7624402 (term26 B _98243)). Qed.
Lemma lem7624404 {B : Type'} (_98243 : nat) : (term191 B _98243) = (term9 B _98243).
Proof. exact (MK_COMB (@lem7624400 _98243) (@lem7624403 B _98243)). Qed.
Lemma lem7624405 {B : Type'} (_98243 : nat) : (term190 B _98243) = (term9 B _98243).
Proof. exact (TRANS (@lem7624395 B _98243) (@lem7624404 B _98243)). Qed.
Lemma lem7624406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7624407 {B : Type'} (_98243 : nat) : (term195 B _98243) = (term196 B _98243).
Proof. exact (MK_COMB (@lem7624406) (@lem7624405 B _98243)). Qed.
Lemma lem7624408 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : ((g _98243) = (@dollar A B f _98243)) = ((g _98243) = (@dollar A B f _98243)).
Proof. exact (eq_refl ((g _98243) = (@dollar A B f _98243))). Qed.
Lemma lem7624409 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term233 A B g f _98243) = (term34 A B g f _98243).
Proof. exact (MK_COMB (@lem7624407 B _98243) (@lem7624408 A B g f _98243)). Qed.
Lemma lem7624410 {A B : Type'} (g : nat -> A) (f : cart A B) (_98243 : nat) : (term232 A B g f _98243) = (term34 A B g f _98243).
Proof. exact (TRANS (@lem7624392 A B g f _98243) (@lem7624409 A B g f _98243)). Qed.
Lemma lem7624412 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term9 B i.
Proof. exact (conj (@lem7624282 A B i g f h1) (@lem7624289 A B i g f h1)). Qed.
Lemma lem7624414 {A B : Type'} (_98243 : nat) (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term34 A B g f _98243.
Proof. exact (EQ_MP (@lem7624410 A B g f _98243) (@lem7624389 A B _98243 i g f h1)). Qed.
Lemma lem7624415 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term34 A B g f i.
Proof. exact (@lem7624414 A B i i g f h1). Qed.
Lemma lem7624418 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : (g i) = (@dollar A B f i).
Proof. exact (@lem7624415 A B i g f h1 (@lem7624412 A B i g f h1)). Qed.
Lemma lem7624419 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term221 A B g f i.
Proof. exact (fun h0 : term168 A B g f i => @lem7624418 A B i g f h1). Qed.
Lemma lem7624421 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624422 {A B : Type'} (g : nat -> A) (f : cart A B) (i : nat) : (term221 A B g f i) = ((g i) = (@dollar A B f i)).
Proof. exact (@lem7624421 ((g i) = (@dollar A B f i))). Qed.
Lemma lem7624423 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : (g i) = (@dollar A B f i).
Proof. exact (EQ_MP (@lem7624422 A B g f i) (@lem7624419 A B i g f h1)). Qed.
Lemma lem7624425 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7624426 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7624425 A x). Qed.
Lemma lem7624427 {A : Type'} (g : nat -> A) (i : nat) : (g i) = (g i).
Proof. exact (@lem7624426 A (g i)). Qed.
Lemma lem7624428 {A : Type'} (g : nat -> A) (i : nat) : term234 A g i.
Proof. exact (fun h0 : term235 A g i => @lem7624427 A g i). Qed.
Lemma lem7624430 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624431 {A : Type'} (g : nat -> A) (i : nat) : (term234 A g i) = ((g i) = (g i)).
Proof. exact (@lem7624430 ((g i) = (g i))). Qed.
Lemma lem7624432 {A : Type'} (g : nat -> A) (i : nat) : (g i) = (g i).
Proof. exact (EQ_MP (@lem7624431 A g i) (@lem7624428 A g i)). Qed.
Lemma lem7624450 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7624451 {A : Type'} (y : A) (x : A) (z : A) : (term200 A x y z) = (term201 A y x z).
Proof. exact (@lem7624450 (y = z) (term202 A x z)). Qed.
Lemma lem7624461 {A : Type'} (x : A) (y : A) : (term203 A x y) = (term203 A x y).
Proof. exact (eq_refl (term203 A x y)). Qed.
Lemma lem7624462 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term204 A y x z).
Proof. exact (MK_COMB (@lem7624461 A x y) (@lem7624451 A y x z)). Qed.
Lemma lem7624466 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7624467 {A : Type'} (y : A) (x : A) (z : A) : (term204 A y x z) = (term205 A y x z).
Proof. exact (@lem7624466 (y = z) (term202 A x y) (term202 A x z)). Qed.
Lemma lem7624489 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term205 A y x z).
Proof. exact (TRANS (@lem7624462 A y x z) (@lem7624467 A y x z)). Qed.
Lemma lem7624490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7624491 {A : Type'} (y : A) (x : A) (z : A) : (term206 A x y z) = (term207 A y x z).
Proof. exact (MK_COMB (@lem7624490) (@lem7624489 A y x z)). Qed.
Lemma lem7624513 {A : Type'} (y : A) (x : A) (z : A) : (term205 A y x z) = (term205 A y x z).
Proof. exact (eq_refl (term205 A y x z)). Qed.
Lemma lem7624514 {A : Type'} (y : A) (x : A) (z : A) : ((term171 A x y z) = (term205 A y x z)) = ((term205 A y x z) = (term205 A y x z)).
Proof. exact (MK_COMB (@lem7624491 A y x z) (@lem7624513 A y x z)). Qed.
Lemma lem7624516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7624517 (x : Prop) : (x = x) = True.
Proof. exact (@lem7624516 Prop x). Qed.
Lemma lem7624518 {A : Type'} (y : A) (x : A) (z : A) : ((term205 A y x z) = (term205 A y x z)) = True.
Proof. exact (@lem7624517 (term205 A y x z)). Qed.
Lemma lem7624519 {A : Type'} (y : A) (x : A) (z : A) : ((term171 A x y z) = (term205 A y x z)) = True.
Proof. exact (TRANS (@lem7624514 A y x z) (@lem7624518 A y x z)). Qed.
Lemma lem7624520 {A : Type'} (y : A) (x : A) (z : A) : True = ((term171 A x y z) = (term205 A y x z)).
Proof. exact (SYM (@lem7624519 A y x z)). Qed.
Lemma lem7624521 {A : Type'} (y : A) (x : A) (z : A) : (term171 A x y z) = (term205 A y x z).
Proof. exact (EQ_MP (@lem7624520 A y x z) (@lem0)). Qed.
Lemma lem7624522 {A : Type'} (y : A) (x : A) (z : A) : term205 A y x z.
Proof. exact (EQ_MP (@lem7624521 A y x z) (@lem7624269 A x y z)). Qed.
Lemma lem7624524 (b : Prop) (a : Prop) : (a \/ b) = (term186 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7624525 {A : Type'} (x : A) (y : A) (z : A) : (term205 A y x z) = (term208 A x y z).
Proof. exact (@lem7624524 (term209 A y x z) (y = z)). Qed.
Lemma lem7624527 (a : Prop) (b : Prop) : (term188 a b) = (term189 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7624528 {A : Type'} (y : A) (x : A) (z : A) : (term210 A y x z) = (term211 A y x z).
Proof. exact (@lem7624527 (term202 A x y) (term202 A x z)). Qed.
Lemma lem7624530 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624531 {A : Type'} (x : A) (y : A) : (term212 A x y) = (x = y).
Proof. exact (@lem7624530 (x = y)). Qed.
Lemma lem7624532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7624533 {A : Type'} (x : A) (y : A) : (term213 A x y) = (term214 A x y).
Proof. exact (MK_COMB (@lem7624532) (@lem7624531 A x y)). Qed.
Lemma lem7624535 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7624536 {A : Type'} (x : A) (z : A) : (term212 A x z) = (x = z).
Proof. exact (@lem7624535 (x = z)). Qed.
Lemma lem7624537 {A : Type'} (y : A) (x : A) (z : A) : (term211 A y x z) = (term215 A y x z).
Proof. exact (MK_COMB (@lem7624533 A x y) (@lem7624536 A x z)). Qed.
Lemma lem7624538 {A : Type'} (y : A) (x : A) (z : A) : (term210 A y x z) = (term215 A y x z).
Proof. exact (TRANS (@lem7624528 A y x z) (@lem7624537 A y x z)). Qed.
Lemma lem7624539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7624540 {A : Type'} (y : A) (x : A) (z : A) : (term216 A y x z) = (term217 A y x z).
Proof. exact (MK_COMB (@lem7624539) (@lem7624538 A y x z)). Qed.
Lemma lem7624541 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7624542 {A : Type'} (x : A) (y : A) (z : A) : (term208 A x y z) = (term218 A x y z).
Proof. exact (MK_COMB (@lem7624540 A y x z) (@lem7624541 A y z)). Qed.
Lemma lem7624543 {A : Type'} (x : A) (y : A) (z : A) : (term205 A y x z) = (term218 A x y z).
Proof. exact (TRANS (@lem7624525 A x y z) (@lem7624542 A x y z)). Qed.
Lemma lem7624545 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term236 A B f g i.
Proof. exact (conj (@lem7624423 A B i g f h1) (@lem7624432 A g i)). Qed.
Lemma lem7624547 {A : Type'} (x : A) (y : A) (z : A) : term218 A x y z.
Proof. exact (EQ_MP (@lem7624543 A x y z) (@lem7624522 A y x z)). Qed.
Lemma lem7624548 {A : Type'} (x : A) (y : A) (z : A) : term218 A x y z.
Proof. exact (@lem7624547 A x y z). Qed.
Lemma lem7624549 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : term237 A B f g i.
Proof. exact (@lem7624548 A (g i) (@dollar A B f i) (g i)). Qed.
Lemma lem7624552 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : (@dollar A B f i) = (g i).
Proof. exact (@lem7624549 A B f g i (@lem7624545 A B i g f h1)). Qed.
Lemma lem7624553 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term197 A B f g i.
Proof. exact (fun h0 : term170 A B f g i => @lem7624552 A B i g f h1). Qed.
Lemma lem7624555 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624556 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term197 A B f g i) = ((@dollar A B f i) = (g i)).
Proof. exact (@lem7624555 ((@dollar A B f i) = (g i))). Qed.
Lemma lem7624557 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : (@dollar A B f i) = (g i).
Proof. exact (EQ_MP (@lem7624556 A B f g i) (@lem7624553 A B i g f h1)). Qed.
Lemma lem7624560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7624562 {A B : Type'} (f : cart A B) (g : nat -> A) (i : nat) : (term170 A B f g i) = (term238 A B f g i).
Proof. exact (@lem7624560 ((@dollar A B f i) = (g i))). Qed.
Lemma lem7624565 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term238 A B f g i.
Proof. exact (EQ_MP (@lem7624562 A B f g i) (@lem7623825 A B i g f h1)). Qed.
Lemma lem7624568 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : False.
Proof. exact (@lem7624565 A B i g f h1 (@lem7624557 A B i g f h1)). Qed.
Lemma lem7624569 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : term223.
Proof. exact (fun h0 : ~ False => @lem7624568 A B i g f h1). Qed.
Lemma lem7624571 (p : Prop) : (term173 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7624572 : term223 = False.
Proof. exact (@lem7624571 False). Qed.
Lemma lem7624573 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term136 A B i g f) : False.
Proof. exact (EQ_MP (@lem7624572) (@lem7624569 A B i g f h1)). Qed.
Lemma lem7624574 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term159 A B i g f) : False.
Proof. exact (or_elim (@lem7623711 A B i g f h1) (fun h0 : term116 A B g f i => @lem7624201 A B g f i h0) (fun h0 : term136 A B i g f => @lem7624573 A B i g f h0)). Qed.
Lemma lem7624575 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term159 A B i g f) : (term159 A B i g f) = False.
Proof. exact (prop_ext (fun h2 : term159 A B i g f => @lem7624574 A B i g f h1) (fun h2 : False => @lem7623711 A B i g f h1)). Qed.
Lemma lem7624576 {A B : Type'} (i : nat) (g : nat -> A) (f : cart A B) (h1 : term159 A B i g f) : False.
Proof. exact (EQ_MP (@lem7624575 A B i g f h1) (@lem7623711 A B i g f h1)). Qed.
Lemma lem7624577 {A B : Type'} (g : nat -> A) (f : cart A B) (h1 : term59 A B g f) : False.
Proof. exact (ex_elim (@lem7623550 A B g f h1) (fun i : nat => fun h0 : term161 A B g f i => @lem7624576 A B i g f h0)). Qed.
Lemma lem7624578 {A B : Type'} (g : nat -> A) (f : cart A B) (h1 : term59 A B g f) : (term59 A B g f) = False.
Proof. exact (prop_ext (fun h2 : term59 A B g f => @lem7624577 A B g f h1) (fun h2 : False => @lem7623194 A B g f h1)). Qed.
Lemma lem7624579 {A B : Type'} (g : nat -> A) (f : cart A B) (h1 : term59 A B g f) : False.
Proof. exact (EQ_MP (@lem7624578 A B g f h1) (@lem7623194 A B g f h1)). Qed.
Lemma lem7624580 {A B : Type'} (g : nat -> A) (f : cart A B) : term58 A B g f.
Proof. exact (fun h0 : term59 A B g f => @lem7624579 A B g f h0). Qed.
Lemma lem7624581 {A B : Type'} (g : nat -> A) (f : cart A B) : (term39 A B f g) = (term37 A B g f).
Proof. exact (EQ_MP (@lem7623193 A B g f) (@lem7624580 A B g f)). Qed.
Lemma lem7624586 {A B : Type'} (f : cart A B) : term43 A B f.
Proof. exact (fun g : nat -> A => @lem7624581 A B g f). Qed.
Lemma lem7624591 {A B : Type'} : term47 A B.
Proof. exact (fun f : cart A B => @lem7624586 A B f). Qed.
Lemma lem7624592 {A B : Type'} : term49 A B.
Proof. exact (EQ_MP (@lem7623189 A B) (@lem7624591 A B)). Qed.
Lemma lem7624594 {A B : Type'} : term49 A B.
Proof. exact (@lem7623085 A B (@lem7624592 A B)). Qed.
Lemma lem7624595 {A B : Type'} (h1 : term50 A B) : False.
Proof. exact (@lem7624594 A B (@lem7623069 A B h1)). Qed.
Lemma lem7624596 {A B : Type'} (h1 : term50 A B) : (term50 A B) = False.
Proof. exact (prop_ext (fun h2 : term50 A B => @lem7624595 A B h1) (fun h2 : False => @lem7623069 A B h1)). Qed.
Lemma lem7624597 {A B : Type'} (h1 : term50 A B) : False.
Proof. exact (EQ_MP (@lem7624596 A B h1) (@lem7623069 A B h1)). Qed.
Lemma lem7624598 {A B : Type'} : term49 A B.
Proof. exact (fun h0 : term50 A B => @lem7624597 A B h0). Qed.
Lemma lem7624599 {A B : Type'} : term47 A B.
Proof. exact (EQ_MP (@lem7623068 A B) (@lem7624598 A B)). Qed.
Lemma lem7624600 {A B : Type'} : term46 A B.
Proof. exact (EQ_MP (@lem7623064 A B) (@lem7624599 A B)). Qed.
