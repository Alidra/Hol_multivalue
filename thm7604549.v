Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7604549_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7603491_spec.
Lemma lem7603580 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7603581 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem7603580 (term1 A)). Qed.
Lemma lem7603582 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem7603581 A)). Qed.
Lemma lem7603583 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7603584 {A : Type'} : term4 A.
Proof. exact (@lem7603491 A). Qed.
Lemma lem7603590 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7603591 {A : Type'} : term6 A.
Proof. exact (fun h0 : term5 A => @lem7603590 A h0). Qed.
Lemma lem7603592 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7603593 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem7603594 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7603592 A h2 (@lem7603593 A h1)). Qed.
Lemma lem7603595 {A : Type'} (h1 : term5 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem7603594 A h1 h0). Qed.
Lemma lem7603596 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7603597 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem7603595 A h1 (@lem7603596 A h2)). Qed.
Lemma lem7603598 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun h0 : term5 A => @lem7603597 A h0 h1). Qed.
Lemma lem7603599 {A : Type'} : term8 A.
Proof. exact (fun h0 : term6 A => @lem7603598 A h0). Qed.
Lemma lem7603602 {A : Type'} : term6 A.
Proof. exact (@lem7603599 A (@lem7603591 A)). Qed.
Lemma lem7603603 {A : Type'} : term6 A.
Proof. exact (@lem7603602 A). Qed.
Lemma lem7603661 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7603662 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem7603661 (term4 A)). Qed.
Lemma lem7603673 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem7603680 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (MK_COMB (@lem7603673 A) (@lem7603662 A)). Qed.
Lemma lem7603685 {A : Type'} (r : nat) : ((term13 A r) = ((term14 A r) = r)) = ((term13 A r) = ((term14 A r) = r)).
Proof. exact (eq_refl ((term13 A r) = ((term14 A r) = r))). Qed.
Lemma lem7603686 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (fun_ext (fun r : nat => @lem7603685 A r)). Qed.
Lemma lem7603687 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603688 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem7603687) (@lem7603686 A)). Qed.
Lemma lem7603689 {A : Type'} (a : finite_image A) : ((term17 A a) = a) = ((term17 A a) = a).
Proof. exact (eq_refl ((term17 A a) = a)). Qed.
Lemma lem7603690 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7603689 A a)). Qed.
Lemma lem7603691 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7603692 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7603691 A) (@lem7603690 A)). Qed.
Lemma lem7603693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603694 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7603693) (@lem7603692 A)). Qed.
Lemma lem7603695 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem7603694 A) (@lem7603688 A)). Qed.
Lemma lem7603696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7603697 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7603696) (@lem7603695 A)). Qed.
Lemma lem7603702 {A : Type'} (x : finite_image A) (x' : nat) : (term21 A x x') = (term21 A x x').
Proof. exact (eq_refl (term21 A x x')). Qed.
Lemma lem7603703 {A : Type'} (x : finite_image A) : (term22 A x) = (term22 A x).
Proof. exact (fun_ext (fun x' : nat => @lem7603702 A x x')). Qed.
Lemma lem7603704 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7603705 {A : Type'} (x : finite_image A) : (term23 A x) = (term23 A x).
Proof. exact (MK_COMB (@lem7603704) (@lem7603703 A x)). Qed.
Lemma lem7603706 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (fun_ext (fun x : finite_image A => @lem7603705 A x)). Qed.
Lemma lem7603707 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7603708 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem7603707 A) (@lem7603706 A)). Qed.
Lemma lem7603709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7603710 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem7603709) (@lem7603708 A)). Qed.
Lemma lem7603711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7603712 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7603711) (@lem7603710 A)). Qed.
Lemma lem7603713 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7603712 A) (@lem7603697 A)). Qed.
Lemma lem7603746 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (TRANS (@lem7603680 A) (@lem7603713 A)). Qed.
Lemma lem7603747 {A : Type'} : (term12 A) = (term5 A).
Proof. exact (SYM (@lem7603746 A)). Qed.
Lemma lem7603748 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7603749 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem7603756 {A : Type'} (x : finite_image A) (x' : nat) : (term25 A x x') = (term26 A x x').
Proof. exact (@lem17045 (x = (@finite_index A x')) (term13 A x')). Qed.
Lemma lem7603757 (P : nat -> Prop) : (term27 P) = (term28 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7603758 {A : Type'} (x : finite_image A) : (term29 A x) = (term30 A x).
Proof. exact (@lem7603757 (term22 A x)). Qed.
Lemma lem7603759 {A : Type'} (x : finite_image A) (x' : nat) : (term31 A x x') = (term21 A x x').
Proof. exact (eq_refl (term31 A x x')). Qed.
Lemma lem7603760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7603761 {A : Type'} (x : finite_image A) (x' : nat) : (term32 A x x') = (term25 A x x').
Proof. exact (MK_COMB (@lem7603760) (@lem7603759 A x x')). Qed.
Lemma lem7603762 {A : Type'} (x : finite_image A) (x' : nat) : (term32 A x x') = (term26 A x x').
Proof. exact (TRANS (@lem7603761 A x x') (@lem7603756 A x x')). Qed.
Lemma lem7603763 {A : Type'} (x : finite_image A) : (term33 A x) = (term34 A x).
Proof. exact (fun_ext (fun x' : nat => @lem7603762 A x x')). Qed.
Lemma lem7603764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603765 {A : Type'} (x : finite_image A) : (term30 A x) = (term35 A x).
Proof. exact (MK_COMB (@lem7603764) (@lem7603763 A x)). Qed.
Lemma lem7603766 {A : Type'} (x : finite_image A) : (term29 A x) = (term35 A x).
Proof. exact (TRANS (@lem7603758 A x) (@lem7603765 A x)). Qed.
Lemma lem7603767 {A : Type'} (P : type33 A) : (term36 A P) = (term37 A P).
Proof. exact (@lem18392 (finite_image A) P). Qed.
Lemma lem7603768 {A : Type'} : (term3 A) = (term38 A).
Proof. exact (@lem7603767 A (term24 A)). Qed.
Lemma lem7603769 {A : Type'} (x : finite_image A) : (term39 A x) = (term23 A x).
Proof. exact (eq_refl (term39 A x)). Qed.
Lemma lem7603770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7603771 {A : Type'} (x : finite_image A) : (term40 A x) = (term29 A x).
Proof. exact (MK_COMB (@lem7603770) (@lem7603769 A x)). Qed.
Lemma lem7603772 {A : Type'} (x : finite_image A) : (term40 A x) = (term35 A x).
Proof. exact (TRANS (@lem7603771 A x) (@lem7603766 A x)). Qed.
Lemma lem7603773 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (fun_ext (fun x : finite_image A => @lem7603772 A x)). Qed.
Lemma lem7603774 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7603775 {A : Type'} : (term38 A) = (term43 A).
Proof. exact (MK_COMB (@lem7603774 A) (@lem7603773 A)). Qed.
Lemma lem7603832 {A : Type'} : (term3 A) = (term43 A).
Proof. exact (TRANS (@lem7603768 A) (@lem7603775 A)). Qed.
Lemma lem7603833 {A : Type'} (h1 : term3 A) : term43 A.
Proof. exact (EQ_MP (@lem7603832 A) (@lem7603748 A h1)). Qed.
Lemma lem7603834 {A : Type'} (a : finite_image A) : ((term17 A a) = a) = ((term17 A a) = a).
Proof. exact (eq_refl ((term17 A a) = a)). Qed.
Lemma lem7603835 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7603834 A a)). Qed.
Lemma lem7603836 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7603837 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7603836 A) (@lem7603835 A)). Qed.
Lemma lem7603852 {A : Type'} (r : nat) : ((term13 A r) = ((term14 A r) = r)) = (term44 A r).
Proof. exact (@lem17784 (term13 A r) ((term14 A r) = r)). Qed.
Lemma lem7603853 {A : Type'} : (term15 A) = (term45 A).
Proof. exact (fun_ext (fun r : nat => @lem7603852 A r)). Qed.
Lemma lem7603854 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603855 {A : Type'} : (term16 A) = (term46 A).
Proof. exact (MK_COMB (@lem7603854) (@lem7603853 A)). Qed.
Lemma lem7603856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603857 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7603856) (@lem7603837 A)). Qed.
Lemma lem7603858 {A : Type'} : (term4 A) = (term47 A).
Proof. exact (MK_COMB (@lem7603857 A) (@lem7603855 A)). Qed.
Lemma lem7603864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7603865 (P : nat -> Prop) (Q : nat -> Prop) : (term50 P Q) = (term51 P Q).
Proof. exact (@lem7603864 nat P Q). Qed.
Lemma lem7603866 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (@lem7603865 (term54 A) (term55 A)). Qed.
Lemma lem7603867 {A : Type'} (r : nat) : (term56 A r) = (term57 A r).
Proof. exact (eq_refl (term56 A r)). Qed.
Lemma lem7603868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603869 {A : Type'} (r : nat) : (term58 A r) = (term59 A r).
Proof. exact (MK_COMB (@lem7603868) (@lem7603867 A r)). Qed.
Lemma lem7603870 {A : Type'} (r : nat) : (term60 A r) = (term61 A r).
Proof. exact (eq_refl (term60 A r)). Qed.
Lemma lem7603871 {A : Type'} (r : nat) : (term62 A r) = (term44 A r).
Proof. exact (MK_COMB (@lem7603869 A r) (@lem7603870 A r)). Qed.
Lemma lem7603872 {A : Type'} : (term63 A) = (term45 A).
Proof. exact (fun_ext (fun r : nat => @lem7603871 A r)). Qed.
Lemma lem7603873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603874 {A : Type'} : (term52 A) = (term46 A).
Proof. exact (MK_COMB (@lem7603873) (@lem7603872 A)). Qed.
Lemma lem7603875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603876 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (MK_COMB (@lem7603875) (@lem7603874 A)). Qed.
Lemma lem7603877 {A : Type'} (r : nat) : (term56 A r) = (term57 A r).
Proof. exact (eq_refl (term56 A r)). Qed.
Lemma lem7603878 {A : Type'} : (term66 A) = (term54 A).
Proof. exact (fun_ext (fun r : nat => @lem7603877 A r)). Qed.
Lemma lem7603879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603880 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (MK_COMB (@lem7603879) (@lem7603878 A)). Qed.
Lemma lem7603881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603882 {A : Type'} : (term69 A) = (term70 A).
Proof. exact (MK_COMB (@lem7603881) (@lem7603880 A)). Qed.
Lemma lem7603883 {A : Type'} (r : nat) : (term60 A r) = (term61 A r).
Proof. exact (eq_refl (term60 A r)). Qed.
Lemma lem7603884 {A : Type'} : (term71 A) = (term55 A).
Proof. exact (fun_ext (fun r : nat => @lem7603883 A r)). Qed.
Lemma lem7603885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7603886 {A : Type'} : (term72 A) = (term73 A).
Proof. exact (MK_COMB (@lem7603885) (@lem7603884 A)). Qed.
Lemma lem7603887 {A : Type'} : (term53 A) = (term74 A).
Proof. exact (MK_COMB (@lem7603882 A) (@lem7603886 A)). Qed.
Lemma lem7603888 {A : Type'} : ((term52 A) = (term53 A)) = ((term46 A) = (term74 A)).
Proof. exact (MK_COMB (@lem7603876 A) (@lem7603887 A)). Qed.
Lemma lem7603889 {A : Type'} : (term46 A) = (term74 A).
Proof. exact (EQ_MP (@lem7603888 A) (@lem7603866 A)). Qed.
Lemma lem7603986 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (eq_refl (term20 A)). Qed.
Lemma lem7603989 {A : Type'} : (term47 A) = (term75 A).
Proof. exact (MK_COMB (@lem7603986 A) (@lem7603889 A)). Qed.
Lemma lem7603990 {A : Type'} : (term4 A) = (term75 A).
Proof. exact (TRANS (@lem7603858 A) (@lem7603989 A)). Qed.
Lemma lem7603991 {A : Type'} (h1 : term4 A) : term75 A.
Proof. exact (EQ_MP (@lem7603990 A) (@lem7603749 A h1)). Qed.
Lemma lem7603992 {A : Type'} (x : finite_image A) (h1 : term35 A x) : term35 A x.
Proof. exact (h1). Qed.
Lemma lem7604021 {A : Type'} (r : nat) : (term61 A r) = (term61 A r).
Proof. exact (eq_refl (term61 A r)). Qed.
Lemma lem7604022 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun r : nat => @lem7604021 A r)). Qed.
Lemma lem7604023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604024 {A : Type'} : (term73 A) = (term73 A).
Proof. exact (MK_COMB (@lem7604023) (@lem7604022 A)). Qed.
Lemma lem7604053 {A : Type'} (r : nat) : (term57 A r) = (term57 A r).
Proof. exact (eq_refl (term57 A r)). Qed.
Lemma lem7604054 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (fun_ext (fun r : nat => @lem7604053 A r)). Qed.
Lemma lem7604055 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604056 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (MK_COMB (@lem7604055) (@lem7604054 A)). Qed.
Lemma lem7604057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604058 {A : Type'} : (term70 A) = (term70 A).
Proof. exact (MK_COMB (@lem7604057) (@lem7604056 A)). Qed.
Lemma lem7604059 {A : Type'} : (term74 A) = (term74 A).
Proof. exact (MK_COMB (@lem7604058 A) (@lem7604024 A)). Qed.
Lemma lem7604068 {A : Type'} (a : finite_image A) : ((term17 A a) = a) = ((term17 A a) = a).
Proof. exact (eq_refl ((term17 A a) = a)). Qed.
Lemma lem7604069 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7604068 A a)). Qed.
Lemma lem7604070 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7604071 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7604070 A) (@lem7604069 A)). Qed.
Lemma lem7604072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604073 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7604072) (@lem7604071 A)). Qed.
Lemma lem7604074 {A : Type'} : (term75 A) = (term75 A).
Proof. exact (MK_COMB (@lem7604073 A) (@lem7604059 A)). Qed.
Lemma lem7604075 {A : Type'} (h1 : term4 A) : term75 A.
Proof. exact (EQ_MP (@lem7604074 A) (@lem7603991 A h1)). Qed.
Lemma lem7604104 {A : Type'} (x : finite_image A) (x' : nat) : (term26 A x x') = (term26 A x x').
Proof. exact (eq_refl (term26 A x x')). Qed.
Lemma lem7604105 {A : Type'} (x : finite_image A) : (term34 A x) = (term34 A x).
Proof. exact (fun_ext (fun x' : nat => @lem7604104 A x x')). Qed.
Lemma lem7604106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604107 {A : Type'} (x : finite_image A) : (term35 A x) = (term35 A x).
Proof. exact (MK_COMB (@lem7604106) (@lem7604105 A x)). Qed.
Lemma lem7604108 {A : Type'} (x : finite_image A) (h1 : term35 A x) : term35 A x.
Proof. exact (EQ_MP (@lem7604107 A x) (@lem7603992 A x h1)). Qed.
Lemma lem7604109 {A : Type'} (h1 : term4 A) : term74 A.
Proof. exact (proj2 (@lem7604075 A h1)). Qed.
Lemma lem7604110 {A : Type'} (h1 : term4 A) : term19 A.
Proof. exact (proj1 (@lem7604075 A h1)). Qed.
Lemma lem7604112 {A : Type'} (h1 : term4 A) : term68 A.
Proof. exact (proj1 (@lem7604109 A h1)). Qed.
Lemma lem7604120 {A : Type'} (x : finite_image A) (x' : nat) : (term26 A x x') = (term26 A x x').
Proof. exact (eq_refl (term26 A x x')). Qed.
Lemma lem7604121 {A : Type'} (x : finite_image A) : (term34 A x) = (term34 A x).
Proof. exact (fun_ext (fun x' : nat => @lem7604120 A x x')). Qed.
Lemma lem7604122 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604124 {A : Type'} (x : finite_image A) : (term35 A x) = (term35 A x).
Proof. exact (MK_COMB (@lem7604122) (@lem7604121 A x)). Qed.
Lemma lem7604125 {A : Type'} (x : finite_image A) (h1 : term35 A x) : term35 A x.
Proof. exact (EQ_MP (@lem7604124 A x) (@lem7604108 A x h1)). Qed.
Lemma lem7604127 {A : Type'} (a : finite_image A) : ((term17 A a) = a) = ((term17 A a) = a).
Proof. exact (eq_refl ((term17 A a) = a)). Qed.
Lemma lem7604128 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7604127 A a)). Qed.
Lemma lem7604129 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7604131 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7604129 A) (@lem7604128 A)). Qed.
Lemma lem7604132 {A : Type'} (h1 : term4 A) : term19 A.
Proof. exact (EQ_MP (@lem7604131 A) (@lem7604110 A h1)). Qed.
Lemma lem7604140 {A : Type'} (r : nat) : (term57 A r) = (term57 A r).
Proof. exact (eq_refl (term57 A r)). Qed.
Lemma lem7604141 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (fun_ext (fun r : nat => @lem7604140 A r)). Qed.
Lemma lem7604142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604144 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (MK_COMB (@lem7604142) (@lem7604141 A)). Qed.
Lemma lem7604145 {A : Type'} (h1 : term4 A) : term68 A.
Proof. exact (EQ_MP (@lem7604144 A) (@lem7604112 A h1)). Qed.
Lemma lem7604159 {A : Type'} (_97766 : nat) (x : finite_image A) (h1 : term35 A x) : term76 A x _97766.
Proof. exact (@lem7604125 A x h1 _97766). Qed.
Lemma lem7604160 {A : Type'} (x : finite_image A) (_97766 : nat) : (term76 A x _97766) = (term26 A x _97766).
Proof. exact (eq_refl (term76 A x _97766)). Qed.
Lemma lem7604162 {A : Type'} (_97767 : finite_image A) (h1 : term4 A) : term77 A _97767.
Proof. exact (@lem7604132 A h1 _97767). Qed.
Lemma lem7604163 {A : Type'} (_97767 : finite_image A) : (term77 A _97767) = ((term17 A _97767) = _97767).
Proof. exact (eq_refl (term77 A _97767)). Qed.
Lemma lem7604165 {A : Type'} (_97768 : nat) (h1 : term4 A) : term56 A _97768.
Proof. exact (@lem7604145 A h1 _97768). Qed.
Lemma lem7604166 {A : Type'} (_97768 : nat) : (term56 A _97768) = (term57 A _97768).
Proof. exact (eq_refl (term56 A _97768)). Qed.
Lemma lem7604176 {A : Type'} (_97766 : nat) (x : finite_image A) (h1 : term35 A x) : term26 A x _97766.
Proof. exact (EQ_MP (@lem7604160 A x _97766) (@lem7604159 A _97766 x h1)). Qed.
Lemma lem7604184 {A : Type'} (_97768 : nat) (h1 : term4 A) : term57 A _97768.
Proof. exact (EQ_MP (@lem7604166 A _97768) (@lem7604165 A _97768 h1)). Qed.
Lemma lem7604210 {A : Type'} : (@dest_finite_image A) = (@dest_finite_image A).
Proof. exact (eq_refl (@dest_finite_image A)). Qed.
Lemma lem7604211 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) (h1 : _97774 = _97775) : _97774 = _97775.
Proof. exact (h1). Qed.
Lemma lem7604212 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) (h1 : _97774 = _97775) : (@dest_finite_image A _97774) = (@dest_finite_image A _97775).
Proof. exact (MK_COMB (@lem7604210 A) (@lem7604211 A _97774 _97775 h1)). Qed.
Lemma lem7604213 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : term78 A _97774 _97775.
Proof. exact (fun h0 : _97774 = _97775 => @lem7604212 A _97774 _97775 h0). Qed.
Lemma lem7604215 (a : Prop) (b : Prop) : (a -> b) = (term79 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7604216 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term78 A _97774 _97775) = (term80 A _97774 _97775).
Proof. exact (@lem7604215 (_97774 = _97775) ((@dest_finite_image A _97774) = (@dest_finite_image A _97775))). Qed.
Lemma lem7604217 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : term80 A _97774 _97775.
Proof. exact (EQ_MP (@lem7604216 A _97774 _97775) (@lem7604213 A _97774 _97775)). Qed.
Lemma lem7604272 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : term81 A x y z.
Proof. exact (@lem21385 (finite_image A) x y z). Qed.
Lemma lem7604274 {A : Type'} (_97767 : finite_image A) (h1 : term4 A) : (term17 A _97767) = _97767.
Proof. exact (EQ_MP (@lem7604163 A _97767) (@lem7604162 A _97767 h1)). Qed.
Lemma lem7604275 {A : Type'} (_97767 : finite_image A) (h1 : term4 A) : (term17 A _97767) = _97767.
Proof. exact (@lem7604274 A _97767 h1). Qed.
Lemma lem7604276 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term17 A x) = x.
Proof. exact (@lem7604275 A x h1). Qed.
Lemma lem7604277 {A : Type'} (x : finite_image A) (h1 : term4 A) : term82 A x.
Proof. exact (fun h0 : term83 A x => @lem7604276 A x h1). Qed.
Lemma lem7604279 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604280 {A : Type'} (x : finite_image A) : (term82 A x) = ((term17 A x) = x).
Proof. exact (@lem7604279 ((term17 A x) = x)). Qed.
Lemma lem7604281 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term17 A x) = x.
Proof. exact (EQ_MP (@lem7604280 A x) (@lem7604277 A x h1)). Qed.
Lemma lem7604283 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem21386 (finite_image A) x). Qed.
Lemma lem7604284 {A : Type'} (x : finite_image A) : x = x.
Proof. exact (@lem7604283 A x). Qed.
Lemma lem7604285 {A : Type'} (x : finite_image A) : (term17 A x) = (term17 A x).
Proof. exact (@lem7604284 A (term17 A x)). Qed.
Lemma lem7604286 {A : Type'} (x : finite_image A) : term85 A x.
Proof. exact (fun h0 : term86 A x => @lem7604285 A x). Qed.
Lemma lem7604288 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604289 {A : Type'} (x : finite_image A) : (term85 A x) = ((term17 A x) = (term17 A x)).
Proof. exact (@lem7604288 ((term17 A x) = (term17 A x))). Qed.
Lemma lem7604290 {A : Type'} (x : finite_image A) : (term17 A x) = (term17 A x).
Proof. exact (EQ_MP (@lem7604289 A x) (@lem7604286 A x)). Qed.
Lemma lem7604308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7604309 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term87 A x y z) = (term88 A y x z).
Proof. exact (@lem7604308 (y = z) (term89 A x z)). Qed.
Lemma lem7604319 {A : Type'} (x : finite_image A) (y : finite_image A) : (term90 A x y) = (term90 A x y).
Proof. exact (eq_refl (term90 A x y)). Qed.
Lemma lem7604320 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term81 A x y z) = (term91 A y x z).
Proof. exact (MK_COMB (@lem7604319 A x y) (@lem7604309 A y x z)). Qed.
Lemma lem7604324 (q : Prop) (p : Prop) (r : Prop) : (term92 p q r) = (term92 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7604325 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term91 A y x z) = (term93 A y x z).
Proof. exact (@lem7604324 (y = z) (term89 A x y) (term89 A x z)). Qed.
Lemma lem7604347 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term81 A x y z) = (term93 A y x z).
Proof. exact (TRANS (@lem7604320 A y x z) (@lem7604325 A y x z)). Qed.
Lemma lem7604348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7604349 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term94 A x y z) = (term95 A y x z).
Proof. exact (MK_COMB (@lem7604348) (@lem7604347 A y x z)). Qed.
Lemma lem7604371 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term93 A y x z) = (term93 A y x z).
Proof. exact (eq_refl (term93 A y x z)). Qed.
Lemma lem7604372 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : ((term81 A x y z) = (term93 A y x z)) = ((term93 A y x z) = (term93 A y x z)).
Proof. exact (MK_COMB (@lem7604349 A y x z) (@lem7604371 A y x z)). Qed.
Lemma lem7604374 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7604375 (x : Prop) : (x = x) = True.
Proof. exact (@lem7604374 Prop x). Qed.
Lemma lem7604376 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : ((term93 A y x z) = (term93 A y x z)) = True.
Proof. exact (@lem7604375 (term93 A y x z)). Qed.
Lemma lem7604377 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : ((term81 A x y z) = (term93 A y x z)) = True.
Proof. exact (TRANS (@lem7604372 A y x z) (@lem7604376 A y x z)). Qed.
Lemma lem7604378 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : True = ((term81 A x y z) = (term93 A y x z)).
Proof. exact (SYM (@lem7604377 A y x z)). Qed.
Lemma lem7604379 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term81 A x y z) = (term93 A y x z).
Proof. exact (EQ_MP (@lem7604378 A y x z) (@lem0)). Qed.
Lemma lem7604380 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : term93 A y x z.
Proof. exact (EQ_MP (@lem7604379 A y x z) (@lem7604272 A x y z)). Qed.
Lemma lem7604382 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7604383 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : (term93 A y x z) = (term97 A x y z).
Proof. exact (@lem7604382 (term98 A y x z) (y = z)). Qed.
Lemma lem7604385 (a : Prop) (b : Prop) : (term99 a b) = (term100 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7604386 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term101 A y x z) = (term102 A y x z).
Proof. exact (@lem7604385 (term89 A x y) (term89 A x z)). Qed.
Lemma lem7604388 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7604389 {A : Type'} (x : finite_image A) (y : finite_image A) : (term104 A x y) = (x = y).
Proof. exact (@lem7604388 (x = y)). Qed.
Lemma lem7604390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604391 {A : Type'} (x : finite_image A) (y : finite_image A) : (term105 A x y) = (term106 A x y).
Proof. exact (MK_COMB (@lem7604390) (@lem7604389 A x y)). Qed.
Lemma lem7604393 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7604394 {A : Type'} (x : finite_image A) (z : finite_image A) : (term104 A x z) = (x = z).
Proof. exact (@lem7604393 (x = z)). Qed.
Lemma lem7604395 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term102 A y x z) = (term107 A y x z).
Proof. exact (MK_COMB (@lem7604391 A x y) (@lem7604394 A x z)). Qed.
Lemma lem7604396 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term101 A y x z) = (term107 A y x z).
Proof. exact (TRANS (@lem7604386 A y x z) (@lem7604395 A y x z)). Qed.
Lemma lem7604397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7604398 {A : Type'} (y : finite_image A) (x : finite_image A) (z : finite_image A) : (term108 A y x z) = (term109 A y x z).
Proof. exact (MK_COMB (@lem7604397) (@lem7604396 A y x z)). Qed.
Lemma lem7604399 {A : Type'} (y : finite_image A) (z : finite_image A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7604400 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : (term97 A x y z) = (term110 A x y z).
Proof. exact (MK_COMB (@lem7604398 A y x z) (@lem7604399 A y z)). Qed.
Lemma lem7604401 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : (term93 A y x z) = (term110 A x y z).
Proof. exact (TRANS (@lem7604383 A x y z) (@lem7604400 A x y z)). Qed.
Lemma lem7604403 {A : Type'} (x : finite_image A) (h1 : term4 A) : term111 A x.
Proof. exact (conj (@lem7604281 A x h1) (@lem7604290 A x)). Qed.
Lemma lem7604405 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : term110 A x y z.
Proof. exact (EQ_MP (@lem7604401 A x y z) (@lem7604380 A y x z)). Qed.
Lemma lem7604406 {A : Type'} (x : finite_image A) (y : finite_image A) (z : finite_image A) : term110 A x y z.
Proof. exact (@lem7604405 A x y z). Qed.
Lemma lem7604407 {A : Type'} (x : finite_image A) : term112 A x.
Proof. exact (@lem7604406 A (term17 A x) x (term17 A x)). Qed.
Lemma lem7604410 {A : Type'} (x : finite_image A) (h1 : term4 A) : x = (term17 A x).
Proof. exact (@lem7604407 A x (@lem7604403 A x h1)). Qed.
Lemma lem7604411 {A : Type'} (x : finite_image A) (h1 : term4 A) : x = (term17 A x).
Proof. exact (@lem7604410 A x h1). Qed.
Lemma lem7604412 {A : Type'} (x : finite_image A) (h1 : term4 A) : term113 A x.
Proof. exact (fun h0 : term114 A x => @lem7604411 A x h1). Qed.
Lemma lem7604414 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604415 {A : Type'} (x : finite_image A) : (term113 A x) = (x = (term17 A x)).
Proof. exact (@lem7604414 (x = (term17 A x))). Qed.
Lemma lem7604416 {A : Type'} (x : finite_image A) (h1 : term4 A) : x = (term17 A x).
Proof. exact (EQ_MP (@lem7604415 A x) (@lem7604412 A x h1)). Qed.
Lemma lem7604418 {A : Type'} (_97767 : finite_image A) (h1 : term4 A) : (term17 A _97767) = _97767.
Proof. exact (EQ_MP (@lem7604163 A _97767) (@lem7604162 A _97767 h1)). Qed.
Lemma lem7604419 {A : Type'} (_97767 : finite_image A) (h1 : term4 A) : (term17 A _97767) = _97767.
Proof. exact (@lem7604418 A _97767 h1). Qed.
Lemma lem7604420 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term17 A x) = x.
Proof. exact (@lem7604419 A x h1). Qed.
Lemma lem7604421 {A : Type'} (x : finite_image A) (h1 : term4 A) : term82 A x.
Proof. exact (fun h0 : term83 A x => @lem7604420 A x h1). Qed.
Lemma lem7604423 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604424 {A : Type'} (x : finite_image A) : (term82 A x) = ((term17 A x) = x).
Proof. exact (@lem7604423 ((term17 A x) = x)). Qed.
Lemma lem7604425 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term17 A x) = x.
Proof. exact (EQ_MP (@lem7604424 A x) (@lem7604421 A x h1)). Qed.
Lemma lem7604431 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7604432 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term80 A _97774 _97775) = (term115 A _97774 _97775).
Proof. exact (@lem7604431 ((@dest_finite_image A _97774) = (@dest_finite_image A _97775)) (term89 A _97774 _97775)). Qed.
Lemma lem7604442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7604443 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term116 A _97774 _97775) = (term117 A _97774 _97775).
Proof. exact (MK_COMB (@lem7604442) (@lem7604432 A _97774 _97775)). Qed.
Lemma lem7604453 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term115 A _97774 _97775) = (term115 A _97774 _97775).
Proof. exact (eq_refl (term115 A _97774 _97775)). Qed.
Lemma lem7604454 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : ((term80 A _97774 _97775) = (term115 A _97774 _97775)) = ((term115 A _97774 _97775) = (term115 A _97774 _97775)).
Proof. exact (MK_COMB (@lem7604443 A _97774 _97775) (@lem7604453 A _97774 _97775)). Qed.
Lemma lem7604456 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7604457 (x : Prop) : (x = x) = True.
Proof. exact (@lem7604456 Prop x). Qed.
Lemma lem7604458 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : ((term115 A _97774 _97775) = (term115 A _97774 _97775)) = True.
Proof. exact (@lem7604457 (term115 A _97774 _97775)). Qed.
Lemma lem7604459 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : ((term80 A _97774 _97775) = (term115 A _97774 _97775)) = True.
Proof. exact (TRANS (@lem7604454 A _97774 _97775) (@lem7604458 A _97774 _97775)). Qed.
Lemma lem7604460 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : True = ((term80 A _97774 _97775) = (term115 A _97774 _97775)).
Proof. exact (SYM (@lem7604459 A _97774 _97775)). Qed.
Lemma lem7604461 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term80 A _97774 _97775) = (term115 A _97774 _97775).
Proof. exact (EQ_MP (@lem7604460 A _97774 _97775) (@lem0)). Qed.
Lemma lem7604462 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : term115 A _97774 _97775.
Proof. exact (EQ_MP (@lem7604461 A _97774 _97775) (@lem7604217 A _97774 _97775)). Qed.
Lemma lem7604464 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7604465 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term115 A _97774 _97775) = (term118 A _97774 _97775).
Proof. exact (@lem7604464 (term89 A _97774 _97775) ((@dest_finite_image A _97774) = (@dest_finite_image A _97775))). Qed.
Lemma lem7604467 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7604468 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term104 A _97774 _97775) = (_97774 = _97775).
Proof. exact (@lem7604467 (_97774 = _97775)). Qed.
Lemma lem7604469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7604470 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term119 A _97774 _97775) = (term120 A _97774 _97775).
Proof. exact (MK_COMB (@lem7604469) (@lem7604468 A _97774 _97775)). Qed.
Lemma lem7604471 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : ((@dest_finite_image A _97774) = (@dest_finite_image A _97775)) = ((@dest_finite_image A _97774) = (@dest_finite_image A _97775)).
Proof. exact (eq_refl ((@dest_finite_image A _97774) = (@dest_finite_image A _97775))). Qed.
Lemma lem7604472 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term118 A _97774 _97775) = (term78 A _97774 _97775).
Proof. exact (MK_COMB (@lem7604470 A _97774 _97775) (@lem7604471 A _97774 _97775)). Qed.
Lemma lem7604473 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : (term115 A _97774 _97775) = (term78 A _97774 _97775).
Proof. exact (TRANS (@lem7604465 A _97774 _97775) (@lem7604472 A _97774 _97775)). Qed.
Lemma lem7604476 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : term78 A _97774 _97775.
Proof. exact (EQ_MP (@lem7604473 A _97774 _97775) (@lem7604462 A _97774 _97775)). Qed.
Lemma lem7604477 {A : Type'} (_97774 : finite_image A) (_97775 : finite_image A) : term78 A _97774 _97775.
Proof. exact (@lem7604476 A _97774 _97775). Qed.
Lemma lem7604478 {A : Type'} (x : finite_image A) : term121 A x.
Proof. exact (@lem7604477 A (term17 A x) x). Qed.
Lemma lem7604481 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term122 A x) = (@dest_finite_image A x).
Proof. exact (@lem7604478 A x (@lem7604425 A x h1)). Qed.
Lemma lem7604482 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term122 A x) = (@dest_finite_image A x).
Proof. exact (@lem7604481 A x h1). Qed.
Lemma lem7604483 {A : Type'} (x : finite_image A) (h1 : term4 A) : term123 A x.
Proof. exact (fun h0 : term124 A x => @lem7604482 A x h1). Qed.
Lemma lem7604485 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604486 {A : Type'} (x : finite_image A) : (term123 A x) = ((term122 A x) = (@dest_finite_image A x)).
Proof. exact (@lem7604485 ((term122 A x) = (@dest_finite_image A x))). Qed.
Lemma lem7604487 {A : Type'} (x : finite_image A) (h1 : term4 A) : (term122 A x) = (@dest_finite_image A x).
Proof. exact (EQ_MP (@lem7604486 A x) (@lem7604483 A x h1)). Qed.
Lemma lem7604489 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7604490 {A : Type'} (_97768 : nat) : (term57 A _97768) = (term125 A _97768).
Proof. exact (@lem7604489 (term126 A _97768) (term13 A _97768)). Qed.
Lemma lem7604492 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7604493 {A : Type'} (_97768 : nat) : (term127 A _97768) = ((term14 A _97768) = _97768).
Proof. exact (@lem7604492 ((term14 A _97768) = _97768)). Qed.
Lemma lem7604494 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7604495 {A : Type'} (_97768 : nat) : (term128 A _97768) = (term129 A _97768).
Proof. exact (MK_COMB (@lem7604494) (@lem7604493 A _97768)). Qed.
Lemma lem7604496 {A : Type'} (_97768 : nat) : (term13 A _97768) = (term13 A _97768).
Proof. exact (eq_refl (term13 A _97768)). Qed.
Lemma lem7604497 {A : Type'} (_97768 : nat) : (term125 A _97768) = (term130 A _97768).
Proof. exact (MK_COMB (@lem7604495 A _97768) (@lem7604496 A _97768)). Qed.
Lemma lem7604498 {A : Type'} (_97768 : nat) : (term57 A _97768) = (term130 A _97768).
Proof. exact (TRANS (@lem7604490 A _97768) (@lem7604497 A _97768)). Qed.
Lemma lem7604501 {A : Type'} (_97768 : nat) (h1 : term4 A) : term130 A _97768.
Proof. exact (EQ_MP (@lem7604498 A _97768) (@lem7604184 A _97768 h1)). Qed.
Lemma lem7604502 {A : Type'} (x : finite_image A) (h1 : term4 A) : term131 A x.
Proof. exact (@lem7604501 A (@dest_finite_image A x) h1). Qed.
Lemma lem7604505 {A : Type'} (x : finite_image A) (h1 : term4 A) : term132 A x.
Proof. exact (@lem7604502 A x h1 (@lem7604487 A x h1)). Qed.
Lemma lem7604506 {A : Type'} (x : finite_image A) (h1 : term4 A) : term132 A x.
Proof. exact (@lem7604505 A x h1). Qed.
Lemma lem7604507 {A : Type'} (x : finite_image A) (h1 : term4 A) : term133 A x.
Proof. exact (fun h0 : term134 A x => @lem7604506 A x h1). Qed.
Lemma lem7604509 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604510 {A : Type'} (x : finite_image A) : (term133 A x) = (term132 A x).
Proof. exact (@lem7604509 (term132 A x)). Qed.
Lemma lem7604511 {A : Type'} (x : finite_image A) (h1 : term4 A) : term132 A x.
Proof. exact (EQ_MP (@lem7604510 A x) (@lem7604507 A x h1)). Qed.
Lemma lem7604513 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7604514 {A : Type'} (x : finite_image A) (_97766 : nat) : (term26 A x _97766) = (term25 A x _97766).
Proof. exact (@lem7604513 (x = (@finite_index A _97766)) (term13 A _97766)). Qed.
Lemma lem7604516 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7604517 {A : Type'} (x : finite_image A) (_97766 : nat) : (term25 A x _97766) = (term137 A x _97766).
Proof. exact (@lem7604516 (term21 A x _97766)). Qed.
Lemma lem7604518 {A : Type'} (x : finite_image A) (_97766 : nat) : (term26 A x _97766) = (term137 A x _97766).
Proof. exact (TRANS (@lem7604514 A x _97766) (@lem7604517 A x _97766)). Qed.
Lemma lem7604520 {A : Type'} (x : finite_image A) (h1 : term4 A) : term138 A x.
Proof. exact (conj (@lem7604416 A x h1) (@lem7604511 A x h1)). Qed.
Lemma lem7604522 {A : Type'} (_97766 : nat) (x : finite_image A) (h1 : term35 A x) : term137 A x _97766.
Proof. exact (EQ_MP (@lem7604518 A x _97766) (@lem7604176 A _97766 x h1)). Qed.
Lemma lem7604523 {A : Type'} (x : finite_image A) (h1 : term35 A x) : term139 A x.
Proof. exact (@lem7604522 A (@dest_finite_image A x) x h1). Qed.
Lemma lem7604526 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : False.
Proof. exact (@lem7604523 A x h1 (@lem7604520 A x h2)). Qed.
Lemma lem7604527 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : term140.
Proof. exact (fun h0 : ~ False => @lem7604526 A x h1 h2). Qed.
Lemma lem7604529 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7604530 : term140 = False.
Proof. exact (@lem7604529 False). Qed.
Lemma lem7604531 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : False.
Proof. exact (EQ_MP (@lem7604530) (@lem7604527 A x h1 h2)). Qed.
Lemma lem7604532 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : (term35 A x) = False.
Proof. exact (prop_ext (fun h3 : term35 A x => @lem7604531 A x h1 h2) (fun h3 : False => @lem7604125 A x h1)). Qed.
Lemma lem7604533 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : False.
Proof. exact (EQ_MP (@lem7604532 A x h1 h2) (@lem7604125 A x h1)). Qed.
Lemma lem7604534 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : (term35 A x) = False.
Proof. exact (prop_ext (fun h3 : term35 A x => @lem7604533 A x h1 h2) (fun h3 : False => @lem7604108 A x h1)). Qed.
Lemma lem7604535 {A : Type'} (x : finite_image A) (h1 : term35 A x) (h2 : term4 A) : False.
Proof. exact (EQ_MP (@lem7604534 A x h1 h2) (@lem7604108 A x h1)). Qed.
Lemma lem7604536 {A : Type'} (h1 : term3 A) (h2 : term4 A) : False.
Proof. exact (ex_elim (@lem7603833 A h1) (fun x : finite_image A => fun h0 : term42 A x => @lem7604535 A x h0 h2)). Qed.
Lemma lem7604537 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (fun h0 : term4 A => @lem7604536 A h1 h0). Qed.
Lemma lem7604538 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem7604539 {A : Type'} (h1 : term3 A) : term10 A.
Proof. exact (EQ_MP (@lem7604538 A) (@lem7604537 A h1)). Qed.
Lemma lem7604540 {A : Type'} : term12 A.
Proof. exact (fun h0 : term3 A => @lem7604539 A h0). Qed.
Lemma lem7604541 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem7603747 A) (@lem7604540 A)). Qed.
Lemma lem7604543 {A : Type'} : term5 A.
Proof. exact (@lem7603603 A (@lem7604541 A)). Qed.
Lemma lem7604544 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (@lem7604543 A (@lem7603583 A h1)). Qed.
Lemma lem7604545 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem7604544 A h1 (@lem7603584 A)). Qed.
Lemma lem7604546 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem7604545 A h1) (fun h2 : False => @lem7603583 A h1)). Qed.
Lemma lem7604547 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem7604546 A h1) (@lem7603583 A h1)). Qed.
Lemma lem7604548 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem7604547 A h0). Qed.
Lemma lem7604549 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem7603582 A) (@lem7604548 A)). Qed.
