Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DELTA_term_abbrevs.
Require Import ITERATE_DELTA_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7123533 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7123535 {_121513 _121532 : Type'} (op : type1400 _121513) : term0 _121513 _121532 op.
Proof. exact (@lem5825973 _121513 _121532 op). Qed.
Lemma lem7123536 {_121513 _121532 : Type'} (op : type1400 _121513) : (term0 _121513 _121532 op) = (term1 _121513 _121532 op).
Proof. exact (eq_refl (term0 _121513 _121532 op)). Qed.
Lemma lem7123537 {_121513 _121532 : Type'} (op : type1400 _121513) : term1 _121513 _121532 op.
Proof. exact (EQ_MP (@lem7123536 _121513 _121532 op) (@lem7123535 _121513 _121532 op)). Qed.
Lemma lem7123538 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (h1). Qed.
Lemma lem7123539 {_121513 _121532 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : term2 _121513 _121532 op.
Proof. exact (@lem7123537 _121513 _121532 op (@lem7123538 _121513 op h1)). Qed.
Lemma lem7123540 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term3 _121513 _121532 op f.
Proof. exact (@lem7123539 _121513 _121532 op h1 f). Qed.
Lemma lem7123541 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term3 _121513 _121532 op f) = (term4 _121513 _121532 f op).
Proof. exact (eq_refl (term3 _121513 _121532 op f)). Qed.
Lemma lem7123542 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term4 _121513 _121532 f op.
Proof. exact (EQ_MP (@lem7123541 _121513 _121532 f op) (@lem7123540 _121513 _121532 f op h1)). Qed.
Lemma lem7123543 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term5 _121513 _121532 f op a.
Proof. exact (@lem7123542 _121513 _121532 f op h1 a). Qed.
Lemma lem7123544 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term5 _121513 _121532 f op a) = (term6 _121513 _121532 f a op).
Proof. exact (eq_refl (term5 _121513 _121532 f op a)). Qed.
Lemma lem7123545 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term6 _121513 _121532 f a op.
Proof. exact (EQ_MP (@lem7123544 _121513 _121532 f a op) (@lem7123543 _121513 _121532 f a op h1)). Qed.
Lemma lem7123546 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (s : _121532 -> Prop) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term7 _121513 _121532 f a op s.
Proof. exact (@lem7123545 _121513 _121532 f a op h1 s). Qed.
Lemma lem7123547 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term7 _121513 _121532 f a op s) = ((term8 _121513 _121532 s a f op) = (term9 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term7 _121513 _121532 f a op s)). Qed.
Lemma lem7123548 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term8 _121513 _121532 s a f op) = (term9 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem7123547 _121513 _121532 s f a op) (@lem7123546 _121513 _121532 f a s op h1)). Qed.
Lemma lem7123554 (h1 : (@neutral real real_add) = term10) : (@neutral real real_add) = term10.
Proof. exact (h1). Qed.
Lemma lem7123555 (h1 : (@neutral real real_add) = term10) : term10 = (@neutral real real_add).
Proof. exact (SYM (@lem7123554 h1)). Qed.
Lemma lem7123556 (h1 : term10 = (@neutral real real_add)) : term10 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7123557 (h1 : term10 = (@neutral real real_add)) : (@neutral real real_add) = term10.
Proof. exact (SYM (@lem7123556 h1)). Qed.
Lemma lem7123558 : ((@neutral real real_add) = term10) = (term10 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term10 => @lem7123555 h1) (fun h1 : term10 = (@neutral real real_add) => @lem7123557 h1)). Qed.
Lemma lem7123571 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7123572 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7123571 A). Qed.
Lemma lem7123573 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7123574 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7123572 A) (@lem7123573 A s)). Qed.
Lemma lem7123580 : term10 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7123558) (@lem7065438)). Qed.
Lemma lem7123581 {A : Type'} (x : A) (a : A) (b : real) : (term11 A x a b) = (term11 A x a b).
Proof. exact (eq_refl (term11 A x a b)). Qed.
Lemma lem7123582 {A : Type'} (x : A) (a : A) (b : real) : (term12 A x a b) = (term13 A x a b).
Proof. exact (MK_COMB (@lem7123581 A x a b) (@lem7123580)). Qed.
Lemma lem7123585 {A : Type'} (a : A) (b : real) : (term14 A a b) = (term15 A a b).
Proof. exact (fun_ext (fun x : A => @lem7123582 A x a b)). Qed.
Lemma lem7123586 {A : Type'} (s : A -> Prop) (a : A) (b : real) : (term16 A s a b) = (term17 A s a b).
Proof. exact (MK_COMB (@lem7123574 A s) (@lem7123585 A a b)). Qed.
Lemma lem7123587 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123588 {A : Type'} (s : A -> Prop) (a : A) (b : real) : (term18 A s a b) = (term19 A s a b).
Proof. exact (MK_COMB (@lem7123587) (@lem7123586 A s a b)). Qed.
Lemma lem7123590 : term10 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7123558) (@lem7065438)). Qed.
Lemma lem7123591 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term20 A a s b) = (term20 A a s b).
Proof. exact (eq_refl (term20 A a s b)). Qed.
Lemma lem7123592 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term21 A a s b) = (term22 A a s b).
Proof. exact (MK_COMB (@lem7123591 A a s b) (@lem7123590)). Qed.
Lemma lem7123593 {A : Type'} (a : A) (s : A -> Prop) (b : real) : ((term16 A s a b) = (term21 A a s b)) = ((term17 A s a b) = (term22 A a s b)).
Proof. exact (MK_COMB (@lem7123588 A s a b) (@lem7123592 A a s b)). Qed.
Lemma lem7123596 {A : Type'} (s : A -> Prop) (b : real) : (term23 A s b) = (term24 A s b).
Proof. exact (fun_ext (fun a : A => @lem7123593 A a s b)). Qed.
Lemma lem7123597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7123598 {A : Type'} (s : A -> Prop) (b : real) : (term25 A s b) = (term26 A s b).
Proof. exact (MK_COMB (@lem7123597 A) (@lem7123596 A s b)). Qed.
Lemma lem7123603 {A : Type'} (b : real) : (term27 A b) = (term28 A b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7123598 A s b)). Qed.
Lemma lem7123604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7123605 {A : Type'} (b : real) : (term29 A b) = (term30 A b).
Proof. exact (MK_COMB (@lem7123604 A) (@lem7123603 A b)). Qed.
Lemma lem7123610 {A : Type'} (b : real) : (term30 A b) = (term29 A b).
Proof. exact (SYM (@lem7123605 A b)). Qed.
Lemma lem7123622 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : term31 _121513 _121532 s f a op.
Proof. exact (fun h0 : @monoidal _121513 op => @lem7123548 _121513 _121532 s f a op h0). Qed.
Lemma lem7123623 {A : Type'} (s : A -> Prop) (f : A -> real) (a : A) (op : type1627) : term32 A s f a op.
Proof. exact (@lem7123622 real A s f a op). Qed.
Lemma lem7123624 {A : Type'} (s : A -> Prop) (b : real) (a : A) : term33 A s b a.
Proof. exact (@lem7123623 A s (term34 A b) a real_add). Qed.
Lemma lem7123625 {A : Type'} (x : A) (b : real) : (term35 A b x) = b.
Proof. exact (eq_refl (term35 A b x)). Qed.
Lemma lem7123626 {A : Type'} (x : A) (a : A) : (term36 A x a) = (term36 A x a).
Proof. exact (eq_refl (term36 A x a)). Qed.
Lemma lem7123627 {A : Type'} (x : A) (a : A) (b : real) : (term37 A a b x) = (term11 A x a b).
Proof. exact (MK_COMB (@lem7123626 A x a) (@lem7123625 A x b)). Qed.
Lemma lem7123628 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7123629 {A : Type'} (x : A) (a : A) (b : real) : (term38 A a b x) = (term13 A x a b).
Proof. exact (MK_COMB (@lem7123627 A x a b) (@lem7123628)). Qed.
Lemma lem7123630 {A : Type'} (a : A) (b : real) : (term39 A a b) = (term15 A a b).
Proof. exact (fun_ext (fun x : A => @lem7123629 A x a b)). Qed.
Lemma lem7123631 {A : Type'} (s : A -> Prop) : (@iterate real A real_add s) = (@iterate real A real_add s).
Proof. exact (eq_refl (@iterate real A real_add s)). Qed.
Lemma lem7123632 {A : Type'} (s : A -> Prop) (a : A) (b : real) : (term40 A s a b) = (term17 A s a b).
Proof. exact (MK_COMB (@lem7123631 A s) (@lem7123630 A a b)). Qed.
Lemma lem7123633 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123634 {A : Type'} (s : A -> Prop) (a : A) (b : real) : (term41 A s a b) = (term19 A s a b).
Proof. exact (MK_COMB (@lem7123633) (@lem7123632 A s a b)). Qed.
Lemma lem7123635 {A : Type'} (a : A) (b : real) : (term35 A b a) = b.
Proof. exact (eq_refl (term35 A b a)). Qed.
Lemma lem7123636 {A : Type'} (a : A) (s : A -> Prop) : (term42 A a s) = (term42 A a s).
Proof. exact (eq_refl (term42 A a s)). Qed.
Lemma lem7123637 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term43 A s b a) = (term20 A a s b).
Proof. exact (MK_COMB (@lem7123636 A a s) (@lem7123635 A a b)). Qed.
Lemma lem7123638 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7123639 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term44 A s b a) = (term22 A a s b).
Proof. exact (MK_COMB (@lem7123637 A a s b) (@lem7123638)). Qed.
Lemma lem7123640 {A : Type'} (a : A) (s : A -> Prop) (b : real) : ((term40 A s a b) = (term44 A s b a)) = ((term17 A s a b) = (term22 A a s b)).
Proof. exact (MK_COMB (@lem7123634 A s a b) (@lem7123639 A a s b)). Qed.
Lemma lem7123641 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem7123642 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term33 A s b a) = (term46 A a s b).
Proof. exact (MK_COMB (@lem7123641) (@lem7123640 A a s b)). Qed.
Lemma lem7123643 {A : Type'} (a : A) (s : A -> Prop) (b : real) : term46 A a s b.
Proof. exact (EQ_MP (@lem7123642 A a s b) (@lem7123624 A s b a)). Qed.
Lemma lem7123645 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7123533) (@lem7067132)). Qed.
Lemma lem7123646 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7123645)). Qed.
Lemma lem7123647 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7123646) (@lem0)). Qed.
Lemma lem7123648 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term17 A s a b) = (term22 A a s b).
Proof. exact (@lem7123643 A a s b (@lem7123647)). Qed.
Lemma lem7123682 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123683 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term19 A s a b) = (term47 A a s b).
Proof. exact (MK_COMB (@lem7123682) (@lem7123648 A a s b)). Qed.
Lemma lem7123750 {A : Type'} (a : A) (s : A -> Prop) (b : real) : (term22 A a s b) = (term22 A a s b).
Proof. exact (eq_refl (term22 A a s b)). Qed.
Lemma lem7123751 {A : Type'} (a : A) (s : A -> Prop) (b : real) : ((term17 A s a b) = (term22 A a s b)) = ((term22 A a s b) = (term22 A a s b)).
Proof. exact (MK_COMB (@lem7123683 A a s b) (@lem7123750 A a s b)). Qed.
Lemma lem7123753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7123754 (x : real) : (x = x) = True.
Proof. exact (@lem7123753 real x). Qed.
Lemma lem7123755 {A : Type'} (a : A) (s : A -> Prop) (b : real) : ((term22 A a s b) = (term22 A a s b)) = True.
Proof. exact (@lem7123754 (term22 A a s b)). Qed.
Lemma lem7123756 {A : Type'} (a : A) (s : A -> Prop) (b : real) : ((term17 A s a b) = (term22 A a s b)) = True.
Proof. exact (TRANS (@lem7123751 A a s b) (@lem7123755 A a s b)). Qed.
Lemma lem7123757 {A : Type'} (s : A -> Prop) (b : real) : (term24 A s b) = (term48 A).
Proof. exact (fun_ext (fun a : A => @lem7123756 A a s b)). Qed.
Lemma lem7123758 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7123759 {A : Type'} (s : A -> Prop) (b : real) : (term26 A s b) = (term49 A).
Proof. exact (MK_COMB (@lem7123758 A) (@lem7123757 A s b)). Qed.
Lemma lem7123761 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7123762 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (@lem7123761 A t). Qed.
Lemma lem7123763 {A : Type'} : (term49 A) = True.
Proof. exact (@lem7123762 A True). Qed.
Lemma lem7123764 {A : Type'} (s : A -> Prop) (b : real) : (term26 A s b) = True.
Proof. exact (TRANS (@lem7123759 A s b) (@lem7123763 A)). Qed.
Lemma lem7123765 {A : Type'} (b : real) : (term28 A b) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7123764 A s b)). Qed.
Lemma lem7123766 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7123767 {A : Type'} (b : real) : (term30 A b) = (term52 A).
Proof. exact (MK_COMB (@lem7123766 A) (@lem7123765 A b)). Qed.
Lemma lem7123769 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7123770 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (@lem7123769 (A -> Prop) t). Qed.
Lemma lem7123771 {A : Type'} : (term52 A) = True.
Proof. exact (@lem7123770 A True). Qed.
Lemma lem7123772 {A : Type'} (b : real) : (term30 A b) = True.
Proof. exact (TRANS (@lem7123767 A b) (@lem7123771 A)). Qed.
Lemma lem7123773 {A : Type'} (b : real) : True = (term30 A b).
Proof. exact (SYM (@lem7123772 A b)). Qed.
Lemma lem7123774 {A : Type'} (b : real) : term30 A b.
Proof. exact (EQ_MP (@lem7123773 A b) (@lem0)). Qed.
Lemma lem7123775 {A : Type'} (b : real) : term29 A b.
Proof. exact (EQ_MP (@lem7123610 A b) (@lem7123774 A b)). Qed.
