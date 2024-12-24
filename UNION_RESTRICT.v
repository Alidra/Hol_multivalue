Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_RESTRICT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3238544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3238545 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) : (s = t) = (term0 _84925 s t).
Proof. exact (@lem3238544 _84925 s t). Qed.
Lemma lem3238546 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : ((term1 _84925 s t P) = (term2 _84925 s t P)) = (term3 _84925 s t P).
Proof. exact (@lem3238545 _84925 (term1 _84925 s t P) (term2 _84925 s t P)). Qed.
Lemma lem3238573 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term4 _84925 s P) = (term5 _84925 s P).
Proof. exact (fun_ext (fun t : _84925 -> Prop => @lem3238546 _84925 s t P)). Qed.
Lemma lem3238574 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238575 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term6 _84925 s P) = (term7 _84925 s P).
Proof. exact (MK_COMB (@lem3238574 _84925) (@lem3238573 _84925 s P)). Qed.
Lemma lem3238580 {_84925 : Type'} (P : _84925 -> Prop) : (term8 _84925 P) = (term9 _84925 P).
Proof. exact (fun_ext (fun s : _84925 -> Prop => @lem3238575 _84925 s P)). Qed.
Lemma lem3238581 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238582 {_84925 : Type'} (P : _84925 -> Prop) : (term10 _84925 P) = (term11 _84925 P).
Proof. exact (MK_COMB (@lem3238581 _84925) (@lem3238580 _84925 P)). Qed.
Lemma lem3238587 {_84925 : Type'} : (term12 _84925) = (term13 _84925).
Proof. exact (fun_ext (fun P : _84925 -> Prop => @lem3238582 _84925 P)). Qed.
Lemma lem3238588 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238589 {_84925 : Type'} : (term14 _84925) = (term15 _84925).
Proof. exact (MK_COMB (@lem3238588 _84925) (@lem3238587 _84925)). Qed.
Lemma lem3238594 {_84925 : Type'} : (term15 _84925) = (term14 _84925).
Proof. exact (SYM (@lem3238589 _84925)). Qed.
Lemma lem3238614 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3238615 {_84925 : Type'} (p : _84925 -> Prop) (x : _84925) : (term16 _84925 x p) = (p x).
Proof. exact (@lem3238614 _84925 p x). Qed.
Lemma lem3238616 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term17 _84925 x s t P) = (term18 _84925 s t P x).
Proof. exact (@lem3238615 _84925 (term19 _84925 s t P) x). Qed.
Lemma lem3238617 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term18 _84925 s t P x) = (term20 _84925 s t P x).
Proof. exact (eq_refl (term18 _84925 s t P x)). Qed.
Lemma lem3238618 {_84925 : Type'} (GEN_PVAR_12 : _84925) : (@SETSPEC _84925 GEN_PVAR_12) = (@SETSPEC _84925 GEN_PVAR_12).
Proof. exact (eq_refl (@SETSPEC _84925 GEN_PVAR_12)). Qed.
Lemma lem3238619 {_84925 : Type'} (GEN_PVAR_12 : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term21 _84925 GEN_PVAR_12 s t P x) = (term22 _84925 GEN_PVAR_12 s t P x).
Proof. exact (MK_COMB (@lem3238618 _84925 GEN_PVAR_12) (@lem3238617 _84925 s t P x)). Qed.
Lemma lem3238620 {_84925 : Type'} (x : _84925) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3238621 {_84925 : Type'} (GEN_PVAR_12 : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term23 _84925 GEN_PVAR_12 s t P x) = (term24 _84925 GEN_PVAR_12 s t P x).
Proof. exact (MK_COMB (@lem3238619 _84925 GEN_PVAR_12 s t P x) (@lem3238620 _84925 x)). Qed.
Lemma lem3238622 {_84925 : Type'} (GEN_PVAR_12 : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term25 _84925 GEN_PVAR_12 s t P) = (term26 _84925 GEN_PVAR_12 s t P).
Proof. exact (fun_ext (fun x : _84925 => @lem3238621 _84925 GEN_PVAR_12 s t P x)). Qed.
Lemma lem3238623 {_84925 : Type'} : (@ex _84925) = (@ex _84925).
Proof. exact (eq_refl (@ex _84925)). Qed.
Lemma lem3238624 {_84925 : Type'} (GEN_PVAR_12 : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term27 _84925 GEN_PVAR_12 s t P) = (term28 _84925 GEN_PVAR_12 s t P).
Proof. exact (MK_COMB (@lem3238623 _84925) (@lem3238622 _84925 GEN_PVAR_12 s t P)). Qed.
Lemma lem3238625 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term29 _84925 s t P) = (term30 _84925 s t P).
Proof. exact (fun_ext (fun GEN_PVAR_12 : _84925 => @lem3238624 _84925 GEN_PVAR_12 s t P)). Qed.
Lemma lem3238626 {_84925 : Type'} : (@GSPEC _84925) = (@GSPEC _84925).
Proof. exact (eq_refl (@GSPEC _84925)). Qed.
Lemma lem3238627 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term31 _84925 s t P) = (term1 _84925 s t P).
Proof. exact (MK_COMB (@lem3238626 _84925) (@lem3238625 _84925 s t P)). Qed.
Lemma lem3238628 {_84925 : Type'} (x : _84925) : (@IN _84925 x) = (@IN _84925 x).
Proof. exact (eq_refl (@IN _84925 x)). Qed.
Lemma lem3238629 {_84925 : Type'} (x : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term17 _84925 x s t P) = (term32 _84925 x s t P).
Proof. exact (MK_COMB (@lem3238628 _84925 x) (@lem3238627 _84925 s t P)). Qed.
Lemma lem3238630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238631 {_84925 : Type'} (x : _84925) (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term33 _84925 x s t P) = (term34 _84925 x s t P).
Proof. exact (MK_COMB (@lem3238630) (@lem3238629 _84925 x s t P)). Qed.
Lemma lem3238632 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term18 _84925 s t P x) = (term20 _84925 s t P x).
Proof. exact (eq_refl (term18 _84925 s t P x)). Qed.
Lemma lem3238633 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term17 _84925 x s t P) = (term18 _84925 s t P x)) = ((term32 _84925 x s t P) = (term20 _84925 s t P x)).
Proof. exact (MK_COMB (@lem3238631 _84925 x s t P) (@lem3238632 _84925 s t P x)). Qed.
Lemma lem3238634 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term32 _84925 x s t P) = (term20 _84925 s t P x).
Proof. exact (EQ_MP (@lem3238633 _84925 s t P x) (@lem3238616 _84925 s t P x)). Qed.
Lemma lem3238638 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3238639 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (t : _84925 -> Prop) : (term35 _84925 x s t) = (term36 _84925 s x t).
Proof. exact (@lem3238638 _84925 s x t). Qed.
Lemma lem3238643 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3238644 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (@IN _84925 x P) = (P x).
Proof. exact (@lem3238643 _84925 P x). Qed.
Lemma lem3238645 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (@IN _84925 x s) = (s x).
Proof. exact (@lem3238644 _84925 s x). Qed.
Lemma lem3238646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3238647 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term37 _84925 x s) = (term38 _84925 s x).
Proof. exact (MK_COMB (@lem3238646) (@lem3238645 _84925 s x)). Qed.
Lemma lem3238649 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3238650 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (@IN _84925 x P) = (P x).
Proof. exact (@lem3238649 _84925 P x). Qed.
Lemma lem3238651 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (@IN _84925 x t) = (t x).
Proof. exact (@lem3238650 _84925 t x). Qed.
Lemma lem3238652 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) : (term36 _84925 s x t) = (term39 _84925 s t x).
Proof. exact (MK_COMB (@lem3238647 _84925 s x) (@lem3238651 _84925 t x)). Qed.
Lemma lem3238655 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) : (term35 _84925 x s t) = (term39 _84925 s t x).
Proof. exact (TRANS (@lem3238639 _84925 s x t) (@lem3238652 _84925 s t x)). Qed.
Lemma lem3238656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3238657 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) : (term40 _84925 x s t) = (term41 _84925 s t x).
Proof. exact (MK_COMB (@lem3238656) (@lem3238655 _84925 s t x)). Qed.
Lemma lem3238658 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3238659 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term20 _84925 s t P x) = (term42 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238657 _84925 s t x) (@lem3238658 _84925 P x)). Qed.
Lemma lem3238662 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term32 _84925 x s t P) = (term42 _84925 s t P x).
Proof. exact (TRANS (@lem3238634 _84925 s t P x) (@lem3238659 _84925 s t P x)). Qed.
Lemma lem3238663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238664 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term34 _84925 x s t P) = (term43 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238663) (@lem3238662 _84925 s t P x)). Qed.
Lemma lem3238666 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3238667 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (t : _84925 -> Prop) : (term35 _84925 x s t) = (term36 _84925 s x t).
Proof. exact (@lem3238666 _84925 s x t). Qed.
Lemma lem3238668 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term44 _84925 x s t P) = (term45 _84925 s x t P).
Proof. exact (@lem3238667 _84925 (term46 _84925 s P) x (term46 _84925 t P)). Qed.
Lemma lem3238672 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3238673 {_84925 : Type'} (p : _84925 -> Prop) (x : _84925) : (term16 _84925 x p) = (p x).
Proof. exact (@lem3238672 _84925 p x). Qed.
Lemma lem3238674 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term47 _84925 x s P) = (term48 _84925 s P x).
Proof. exact (@lem3238673 _84925 (term49 _84925 s P) x). Qed.
Lemma lem3238675 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term48 _84925 s P x) = (term50 _84925 s P x).
Proof. exact (eq_refl (term48 _84925 s P x)). Qed.
Lemma lem3238676 {_84925 : Type'} (GEN_PVAR_13 : _84925) : (@SETSPEC _84925 GEN_PVAR_13) = (@SETSPEC _84925 GEN_PVAR_13).
Proof. exact (eq_refl (@SETSPEC _84925 GEN_PVAR_13)). Qed.
Lemma lem3238677 {_84925 : Type'} (GEN_PVAR_13 : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term51 _84925 GEN_PVAR_13 s P x) = (term52 _84925 GEN_PVAR_13 s P x).
Proof. exact (MK_COMB (@lem3238676 _84925 GEN_PVAR_13) (@lem3238675 _84925 s P x)). Qed.
Lemma lem3238678 {_84925 : Type'} (x : _84925) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3238679 {_84925 : Type'} (GEN_PVAR_13 : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term53 _84925 GEN_PVAR_13 s P x) = (term54 _84925 GEN_PVAR_13 s P x).
Proof. exact (MK_COMB (@lem3238677 _84925 GEN_PVAR_13 s P x) (@lem3238678 _84925 x)). Qed.
Lemma lem3238680 {_84925 : Type'} (GEN_PVAR_13 : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) : (term55 _84925 GEN_PVAR_13 s P) = (term56 _84925 GEN_PVAR_13 s P).
Proof. exact (fun_ext (fun x : _84925 => @lem3238679 _84925 GEN_PVAR_13 s P x)). Qed.
Lemma lem3238681 {_84925 : Type'} : (@ex _84925) = (@ex _84925).
Proof. exact (eq_refl (@ex _84925)). Qed.
Lemma lem3238682 {_84925 : Type'} (GEN_PVAR_13 : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) : (term57 _84925 GEN_PVAR_13 s P) = (term58 _84925 GEN_PVAR_13 s P).
Proof. exact (MK_COMB (@lem3238681 _84925) (@lem3238680 _84925 GEN_PVAR_13 s P)). Qed.
Lemma lem3238683 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term59 _84925 s P) = (term60 _84925 s P).
Proof. exact (fun_ext (fun GEN_PVAR_13 : _84925 => @lem3238682 _84925 GEN_PVAR_13 s P)). Qed.
Lemma lem3238684 {_84925 : Type'} : (@GSPEC _84925) = (@GSPEC _84925).
Proof. exact (eq_refl (@GSPEC _84925)). Qed.
Lemma lem3238685 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term61 _84925 s P) = (term46 _84925 s P).
Proof. exact (MK_COMB (@lem3238684 _84925) (@lem3238683 _84925 s P)). Qed.
Lemma lem3238686 {_84925 : Type'} (x : _84925) : (@IN _84925 x) = (@IN _84925 x).
Proof. exact (eq_refl (@IN _84925 x)). Qed.
Lemma lem3238687 {_84925 : Type'} (x : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) : (term47 _84925 x s P) = (term62 _84925 x s P).
Proof. exact (MK_COMB (@lem3238686 _84925 x) (@lem3238685 _84925 s P)). Qed.
Lemma lem3238688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238689 {_84925 : Type'} (x : _84925) (s : _84925 -> Prop) (P : _84925 -> Prop) : (term63 _84925 x s P) = (term64 _84925 x s P).
Proof. exact (MK_COMB (@lem3238688) (@lem3238687 _84925 x s P)). Qed.
Lemma lem3238690 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term48 _84925 s P x) = (term50 _84925 s P x).
Proof. exact (eq_refl (term48 _84925 s P x)). Qed.
Lemma lem3238691 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term47 _84925 x s P) = (term48 _84925 s P x)) = ((term62 _84925 x s P) = (term50 _84925 s P x)).
Proof. exact (MK_COMB (@lem3238689 _84925 x s P) (@lem3238690 _84925 s P x)). Qed.
Lemma lem3238692 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term62 _84925 x s P) = (term50 _84925 s P x).
Proof. exact (EQ_MP (@lem3238691 _84925 s P x) (@lem3238674 _84925 s P x)). Qed.
Lemma lem3238696 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3238697 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (@IN _84925 x P) = (P x).
Proof. exact (@lem3238696 _84925 P x). Qed.
Lemma lem3238698 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (@IN _84925 x s) = (s x).
Proof. exact (@lem3238697 _84925 s x). Qed.
Lemma lem3238699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3238700 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term65 _84925 x s) = (term66 _84925 s x).
Proof. exact (MK_COMB (@lem3238699) (@lem3238698 _84925 s x)). Qed.
Lemma lem3238701 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3238702 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term50 _84925 s P x) = (term67 _84925 s P x).
Proof. exact (MK_COMB (@lem3238700 _84925 s x) (@lem3238701 _84925 P x)). Qed.
Lemma lem3238705 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term62 _84925 x s P) = (term67 _84925 s P x).
Proof. exact (TRANS (@lem3238692 _84925 s P x) (@lem3238702 _84925 s P x)). Qed.
Lemma lem3238706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3238707 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term68 _84925 x s P) = (term69 _84925 s P x).
Proof. exact (MK_COMB (@lem3238706) (@lem3238705 _84925 s P x)). Qed.
Lemma lem3238709 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3238710 {_84925 : Type'} (p : _84925 -> Prop) (x : _84925) : (term16 _84925 x p) = (p x).
Proof. exact (@lem3238709 _84925 p x). Qed.
Lemma lem3238711 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term47 _84925 x t P) = (term48 _84925 t P x).
Proof. exact (@lem3238710 _84925 (term49 _84925 t P) x). Qed.
Lemma lem3238712 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term48 _84925 t P x) = (term50 _84925 t P x).
Proof. exact (eq_refl (term48 _84925 t P x)). Qed.
Lemma lem3238713 {_84925 : Type'} (GEN_PVAR_14 : _84925) : (@SETSPEC _84925 GEN_PVAR_14) = (@SETSPEC _84925 GEN_PVAR_14).
Proof. exact (eq_refl (@SETSPEC _84925 GEN_PVAR_14)). Qed.
Lemma lem3238714 {_84925 : Type'} (GEN_PVAR_14 : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term51 _84925 GEN_PVAR_14 t P x) = (term52 _84925 GEN_PVAR_14 t P x).
Proof. exact (MK_COMB (@lem3238713 _84925 GEN_PVAR_14) (@lem3238712 _84925 t P x)). Qed.
Lemma lem3238715 {_84925 : Type'} (x : _84925) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3238716 {_84925 : Type'} (GEN_PVAR_14 : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term53 _84925 GEN_PVAR_14 t P x) = (term54 _84925 GEN_PVAR_14 t P x).
Proof. exact (MK_COMB (@lem3238714 _84925 GEN_PVAR_14 t P x) (@lem3238715 _84925 x)). Qed.
Lemma lem3238717 {_84925 : Type'} (GEN_PVAR_14 : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term55 _84925 GEN_PVAR_14 t P) = (term56 _84925 GEN_PVAR_14 t P).
Proof. exact (fun_ext (fun x : _84925 => @lem3238716 _84925 GEN_PVAR_14 t P x)). Qed.
Lemma lem3238718 {_84925 : Type'} : (@ex _84925) = (@ex _84925).
Proof. exact (eq_refl (@ex _84925)). Qed.
Lemma lem3238719 {_84925 : Type'} (GEN_PVAR_14 : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term57 _84925 GEN_PVAR_14 t P) = (term58 _84925 GEN_PVAR_14 t P).
Proof. exact (MK_COMB (@lem3238718 _84925) (@lem3238717 _84925 GEN_PVAR_14 t P)). Qed.
Lemma lem3238720 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) : (term59 _84925 t P) = (term60 _84925 t P).
Proof. exact (fun_ext (fun GEN_PVAR_14 : _84925 => @lem3238719 _84925 GEN_PVAR_14 t P)). Qed.
Lemma lem3238721 {_84925 : Type'} : (@GSPEC _84925) = (@GSPEC _84925).
Proof. exact (eq_refl (@GSPEC _84925)). Qed.
Lemma lem3238722 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) : (term61 _84925 t P) = (term46 _84925 t P).
Proof. exact (MK_COMB (@lem3238721 _84925) (@lem3238720 _84925 t P)). Qed.
Lemma lem3238723 {_84925 : Type'} (x : _84925) : (@IN _84925 x) = (@IN _84925 x).
Proof. exact (eq_refl (@IN _84925 x)). Qed.
Lemma lem3238724 {_84925 : Type'} (x : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term47 _84925 x t P) = (term62 _84925 x t P).
Proof. exact (MK_COMB (@lem3238723 _84925 x) (@lem3238722 _84925 t P)). Qed.
Lemma lem3238725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238726 {_84925 : Type'} (x : _84925) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term63 _84925 x t P) = (term64 _84925 x t P).
Proof. exact (MK_COMB (@lem3238725) (@lem3238724 _84925 x t P)). Qed.
Lemma lem3238727 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term48 _84925 t P x) = (term50 _84925 t P x).
Proof. exact (eq_refl (term48 _84925 t P x)). Qed.
Lemma lem3238728 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term47 _84925 x t P) = (term48 _84925 t P x)) = ((term62 _84925 x t P) = (term50 _84925 t P x)).
Proof. exact (MK_COMB (@lem3238726 _84925 x t P) (@lem3238727 _84925 t P x)). Qed.
Lemma lem3238729 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term62 _84925 x t P) = (term50 _84925 t P x).
Proof. exact (EQ_MP (@lem3238728 _84925 t P x) (@lem3238711 _84925 t P x)). Qed.
Lemma lem3238733 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3238734 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (@IN _84925 x P) = (P x).
Proof. exact (@lem3238733 _84925 P x). Qed.
Lemma lem3238735 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (@IN _84925 x t) = (t x).
Proof. exact (@lem3238734 _84925 t x). Qed.
Lemma lem3238736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3238737 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (term65 _84925 x t) = (term66 _84925 t x).
Proof. exact (MK_COMB (@lem3238736) (@lem3238735 _84925 t x)). Qed.
Lemma lem3238738 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3238739 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term50 _84925 t P x) = (term67 _84925 t P x).
Proof. exact (MK_COMB (@lem3238737 _84925 t x) (@lem3238738 _84925 P x)). Qed.
Lemma lem3238742 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term62 _84925 x t P) = (term67 _84925 t P x).
Proof. exact (TRANS (@lem3238729 _84925 t P x) (@lem3238739 _84925 t P x)). Qed.
Lemma lem3238743 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term45 _84925 s x t P) = (term70 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238707 _84925 s P x) (@lem3238742 _84925 t P x)). Qed.
Lemma lem3238746 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term44 _84925 x s t P) = (term70 _84925 s t P x).
Proof. exact (TRANS (@lem3238668 _84925 s x t P) (@lem3238743 _84925 s t P x)). Qed.
Lemma lem3238747 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term32 _84925 x s t P) = (term44 _84925 x s t P)) = ((term42 _84925 s t P x) = (term70 _84925 s t P x)).
Proof. exact (MK_COMB (@lem3238664 _84925 s t P x) (@lem3238746 _84925 s t P x)). Qed.
Lemma lem3238750 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term71 _84925 s t P) = (term72 _84925 s t P).
Proof. exact (fun_ext (fun x : _84925 => @lem3238747 _84925 s t P x)). Qed.
Lemma lem3238751 {_84925 : Type'} : (@all _84925) = (@all _84925).
Proof. exact (eq_refl (@all _84925)). Qed.
Lemma lem3238752 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term3 _84925 s t P) = (term73 _84925 s t P).
Proof. exact (MK_COMB (@lem3238751 _84925) (@lem3238750 _84925 s t P)). Qed.
Lemma lem3238757 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term5 _84925 s P) = (term74 _84925 s P).
Proof. exact (fun_ext (fun t : _84925 -> Prop => @lem3238752 _84925 s t P)). Qed.
Lemma lem3238758 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238759 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term7 _84925 s P) = (term75 _84925 s P).
Proof. exact (MK_COMB (@lem3238758 _84925) (@lem3238757 _84925 s P)). Qed.
Lemma lem3238764 {_84925 : Type'} (P : _84925 -> Prop) : (term9 _84925 P) = (term76 _84925 P).
Proof. exact (fun_ext (fun s : _84925 -> Prop => @lem3238759 _84925 s P)). Qed.
Lemma lem3238765 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238766 {_84925 : Type'} (P : _84925 -> Prop) : (term11 _84925 P) = (term77 _84925 P).
Proof. exact (MK_COMB (@lem3238765 _84925) (@lem3238764 _84925 P)). Qed.
Lemma lem3238771 {_84925 : Type'} : (term13 _84925) = (term78 _84925).
Proof. exact (fun_ext (fun P : _84925 -> Prop => @lem3238766 _84925 P)). Qed.
Lemma lem3238772 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238773 {_84925 : Type'} : (term15 _84925) = (term79 _84925).
Proof. exact (MK_COMB (@lem3238772 _84925) (@lem3238771 _84925)). Qed.
Lemma lem3238778 {_84925 : Type'} : (term79 _84925) = (term15 _84925).
Proof. exact (SYM (@lem3238773 _84925)). Qed.
Lemma lem3238780 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3238781 {_84925 : Type'} : (term79 _84925) = (term81 _84925).
Proof. exact (@lem3238780 (term79 _84925)). Qed.
Lemma lem3238782 {_84925 : Type'} : (term81 _84925) = (term79 _84925).
Proof. exact (SYM (@lem3238781 _84925)). Qed.
Lemma lem3238783 {_84925 : Type'} (h1 : term82 _84925) : term82 _84925.
Proof. exact (h1). Qed.
Lemma lem3238786 {_84925 : Type'} (h1 : term81 _84925) : term81 _84925.
Proof. exact (h1). Qed.
Lemma lem3238787 {_84925 : Type'} : term83 _84925.
Proof. exact (fun h0 : term81 _84925 => @lem3238786 _84925 h0). Qed.
Lemma lem3238788 {_84925 : Type'} (h1 : term83 _84925) : term83 _84925.
Proof. exact (h1). Qed.
Lemma lem3238789 {_84925 : Type'} (h1 : term81 _84925) : term81 _84925.
Proof. exact (h1). Qed.
Lemma lem3238790 {_84925 : Type'} (h1 : term81 _84925) (h2 : term83 _84925) : term81 _84925.
Proof. exact (@lem3238788 _84925 h2 (@lem3238789 _84925 h1)). Qed.
Lemma lem3238791 {_84925 : Type'} (h1 : term81 _84925) : term84 _84925.
Proof. exact (fun h0 : term83 _84925 => @lem3238790 _84925 h1 h0). Qed.
Lemma lem3238792 {_84925 : Type'} (h1 : term83 _84925) : term83 _84925.
Proof. exact (h1). Qed.
Lemma lem3238793 {_84925 : Type'} (h1 : term81 _84925) (h2 : term83 _84925) : term81 _84925.
Proof. exact (@lem3238791 _84925 h1 (@lem3238792 _84925 h2)). Qed.
Lemma lem3238794 {_84925 : Type'} (h1 : term83 _84925) : term83 _84925.
Proof. exact (fun h0 : term81 _84925 => @lem3238793 _84925 h0 h1). Qed.
Lemma lem3238795 {_84925 : Type'} : term85 _84925.
Proof. exact (fun h0 : term83 _84925 => @lem3238794 _84925 h0). Qed.
Lemma lem3238798 {_84925 : Type'} : term83 _84925.
Proof. exact (@lem3238795 _84925 (@lem3238787 _84925)). Qed.
Lemma lem3238799 {_84925 : Type'} : term83 _84925.
Proof. exact (@lem3238798 _84925). Qed.
Lemma lem3238801 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3238802 {_84925 : Type'} : (term81 _84925) = (term86 _84925).
Proof. exact (@lem3238801 (term82 _84925)). Qed.
Lemma lem3238804 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3238805 {_84925 : Type'} : (term86 _84925) = (term79 _84925).
Proof. exact (@lem3238804 (term79 _84925)). Qed.
Lemma lem3238836 {_84925 : Type'} : (term81 _84925) = (term79 _84925).
Proof. exact (TRANS (@lem3238802 _84925) (@lem3238805 _84925)). Qed.
Lemma lem3238861 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term42 _84925 s t P x) = (term70 _84925 s t P x)) = ((term42 _84925 s t P x) = (term70 _84925 s t P x)).
Proof. exact (eq_refl ((term42 _84925 s t P x) = (term70 _84925 s t P x))). Qed.
Lemma lem3238862 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term72 _84925 s t P) = (term72 _84925 s t P).
Proof. exact (fun_ext (fun x : _84925 => @lem3238861 _84925 s t P x)). Qed.
Lemma lem3238863 {_84925 : Type'} : (@all _84925) = (@all _84925).
Proof. exact (eq_refl (@all _84925)). Qed.
Lemma lem3238864 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : (term73 _84925 s t P) = (term73 _84925 s t P).
Proof. exact (MK_COMB (@lem3238863 _84925) (@lem3238862 _84925 s t P)). Qed.
Lemma lem3238865 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term74 _84925 s P) = (term74 _84925 s P).
Proof. exact (fun_ext (fun t : _84925 -> Prop => @lem3238864 _84925 s t P)). Qed.
Lemma lem3238866 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238867 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : (term75 _84925 s P) = (term75 _84925 s P).
Proof. exact (MK_COMB (@lem3238866 _84925) (@lem3238865 _84925 s P)). Qed.
Lemma lem3238868 {_84925 : Type'} (P : _84925 -> Prop) : (term76 _84925 P) = (term76 _84925 P).
Proof. exact (fun_ext (fun s : _84925 -> Prop => @lem3238867 _84925 s P)). Qed.
Lemma lem3238869 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238870 {_84925 : Type'} (P : _84925 -> Prop) : (term77 _84925 P) = (term77 _84925 P).
Proof. exact (MK_COMB (@lem3238869 _84925) (@lem3238868 _84925 P)). Qed.
Lemma lem3238871 {_84925 : Type'} : (term78 _84925) = (term78 _84925).
Proof. exact (fun_ext (fun P : _84925 -> Prop => @lem3238870 _84925 P)). Qed.
Lemma lem3238872 {_84925 : Type'} : (@all (_84925 -> Prop)) = (@all (_84925 -> Prop)).
Proof. exact (eq_refl (@all (_84925 -> Prop))). Qed.
Lemma lem3238873 {_84925 : Type'} : (term79 _84925) = (term79 _84925).
Proof. exact (MK_COMB (@lem3238872 _84925) (@lem3238871 _84925)). Qed.
Lemma lem3238910 {_84925 : Type'} : (term81 _84925) = (term79 _84925).
Proof. exact (TRANS (@lem3238836 _84925) (@lem3238873 _84925)). Qed.
Lemma lem3238911 {_84925 : Type'} : (term79 _84925) = (term81 _84925).
Proof. exact (SYM (@lem3238910 _84925)). Qed.
Lemma lem3238913 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3238914 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : ((term42 _84925 s t P x) = (term70 _84925 s t P x)) = (term88 _84925 s t P x).
Proof. exact (@lem3238913 ((term42 _84925 s t P x) = (term70 _84925 s t P x))). Qed.
Lemma lem3238915 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term88 _84925 s t P x) = ((term42 _84925 s t P x) = (term70 _84925 s t P x)).
Proof. exact (SYM (@lem3238914 _84925 s t P x)). Qed.
Lemma lem3238916 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term89 _84925 s t P x) : term89 _84925 s t P x.
Proof. exact (h1). Qed.
Lemma lem3238925 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) : (term90 _84925 s t x) = (term91 _84925 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3238929 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term92 _84925 P x).
Proof. exact (eq_refl (term92 _84925 P x)). Qed.
Lemma lem3238931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3238932 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) : (term93 _84925 s t x) = (term94 _84925 s t x).
Proof. exact (MK_COMB (@lem3238931) (@lem3238925 _84925 s t x)). Qed.
Lemma lem3238933 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term95 _84925 s t P x) = (term96 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238932 _84925 s t x) (@lem3238929 _84925 P x)). Qed.
Lemma lem3238934 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term97 _84925 s t P x) = (term95 _84925 s t P x).
Proof. exact (@lem17045 (term39 _84925 s t x) (P x)). Qed.
Lemma lem3238935 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term97 _84925 s t P x) = (term96 _84925 s t P x).
Proof. exact (TRANS (@lem3238934 _84925 s t P x) (@lem3238933 _84925 s t P x)). Qed.
Lemma lem3238947 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term98 _84925 s P x) = (term99 _84925 s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem3238959 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term98 _84925 t P x) = (term99 _84925 t P x).
Proof. exact (@lem17045 (t x) (P x)). Qed.
Lemma lem3238963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3238964 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term100 _84925 s P x) = (term101 _84925 s P x).
Proof. exact (MK_COMB (@lem3238963) (@lem3238947 _84925 s P x)). Qed.
Lemma lem3238965 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term102 _84925 s t P x) = (term103 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238964 _84925 s P x) (@lem3238959 _84925 t P x)). Qed.
Lemma lem3238966 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term104 _84925 s t P x) = (term102 _84925 s t P x).
Proof. exact (@lem17160 (term67 _84925 s P x) (term67 _84925 t P x)). Qed.
Lemma lem3238967 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term104 _84925 s t P x) = (term103 _84925 s t P x).
Proof. exact (TRANS (@lem3238966 _84925 s t P x) (@lem3238965 _84925 s t P x)). Qed.
Lemma lem3238970 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term70 _84925 s t P x) = (term70 _84925 s t P x).
Proof. exact (eq_refl (term70 _84925 s t P x)). Qed.
Lemma lem3238971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3238972 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term105 _84925 s t P x) = (term106 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238971) (@lem3238935 _84925 s t P x)). Qed.
Lemma lem3238973 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term107 _84925 s t P x) = (term108 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238972 _84925 s t P x) (@lem3238970 _84925 s t P x)). Qed.
Lemma lem3238975 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term109 _84925 s t P x) = (term109 _84925 s t P x).
Proof. exact (eq_refl (term109 _84925 s t P x)). Qed.
Lemma lem3238976 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term110 _84925 s t P x) = (term111 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238975 _84925 s t P x) (@lem3238967 _84925 s t P x)). Qed.
Lemma lem3238977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3238978 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term112 _84925 s t P x) = (term113 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238977) (@lem3238976 _84925 s t P x)). Qed.
Lemma lem3238979 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term114 _84925 s t P x) = (term115 _84925 s t P x).
Proof. exact (MK_COMB (@lem3238978 _84925 s t P x) (@lem3238973 _84925 s t P x)). Qed.
Lemma lem3238980 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term89 _84925 s t P x) = (term114 _84925 s t P x).
Proof. exact (@lem17646 (term42 _84925 s t P x) (term70 _84925 s t P x)). Qed.
Lemma lem3238985 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term89 _84925 s t P x) = (term115 _84925 s t P x).
Proof. exact (TRANS (@lem3238980 _84925 s t P x) (@lem3238979 _84925 s t P x)). Qed.
Lemma lem3239082 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term89 _84925 s t P x) : term115 _84925 s t P x.
Proof. exact (EQ_MP (@lem3238985 _84925 s t P x) (@lem3238916 _84925 s t P x h1)). Qed.
Lemma lem3239083 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term111 _84925 s t P x.
Proof. exact (h1). Qed.
Lemma lem3239084 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term108 _84925 s t P x) : term108 _84925 s t P x.
Proof. exact (h1). Qed.
Lemma lem3239085 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term103 _84925 s t P x.
Proof. exact (proj2 (@lem3239083 _84925 s t P x h1)). Qed.
Lemma lem3239086 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term42 _84925 s t P x.
Proof. exact (proj1 (@lem3239083 _84925 s t P x h1)). Qed.
Lemma lem3239087 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term99 _84925 t P x.
Proof. exact (proj2 (@lem3239085 _84925 s t P x h1)). Qed.
Lemma lem3239088 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term99 _84925 s P x.
Proof. exact (proj1 (@lem3239085 _84925 s t P x h1)). Qed.
Lemma lem3239090 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term39 _84925 s t x.
Proof. exact (proj1 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239105 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term108 _84925 s t P x) : term70 _84925 s t P x.
Proof. exact (proj2 (@lem3239084 _84925 s t P x h1)). Qed.
Lemma lem3239106 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term108 _84925 s t P x) : term96 _84925 s t P x.
Proof. exact (proj1 (@lem3239084 _84925 s t P x h1)). Qed.
Lemma lem3239107 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : term67 _84925 s P x.
Proof. exact (h1). Qed.
Lemma lem3239108 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : term67 _84925 t P x.
Proof. exact (h1). Qed.
Lemma lem3239111 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term91 _84925 s t x.
Proof. exact (h1). Qed.
Lemma lem3239117 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term91 _84925 s t x.
Proof. exact (h1). Qed.
Lemma lem3239128 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239136 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term92 _84925 s x.
Proof. exact (h1). Qed.
Lemma lem3239152 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239160 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239168 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term92 _84925 s x.
Proof. exact (h1). Qed.
Lemma lem3239180 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239184 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239192 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3239196 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) : term92 _84925 t x.
Proof. exact (h1). Qed.
Lemma lem3239216 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239228 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239244 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239248 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239276 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239304 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239308 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239312 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term92 _84925 s x.
Proof. exact (h1). Qed.
Lemma lem3239320 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239324 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239328 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term92 _84925 s x.
Proof. exact (h1). Qed.
Lemma lem3239334 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239336 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239340 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3239342 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) : term92 _84925 t x.
Proof. exact (h1). Qed.
Lemma lem3239352 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239358 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239366 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239368 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239374 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term92 _84925 s x.
Proof. exact (proj1 (@lem3239111 _84925 s t x h1)). Qed.
Lemma lem3239382 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239390 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term92 _84925 t x.
Proof. exact (proj2 (@lem3239117 _84925 s t x h1)). Qed.
Lemma lem3239396 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term92 _84925 P x.
Proof. exact (h1). Qed.
Lemma lem3239398 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239399 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : term116 _84925 s x.
Proof. exact (fun h0 : term92 _84925 s x => @lem3239398 _84925 s x h1). Qed.
Lemma lem3239401 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239402 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term116 _84925 s x) = (s x).
Proof. exact (@lem3239401 (s x)). Qed.
Lemma lem3239403 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3239402 _84925 s x) (@lem3239399 _84925 s x h1)). Qed.
Lemma lem3239406 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239408 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term92 _84925 s x) = (term118 _84925 s x).
Proof. exact (@lem3239406 (s x)). Qed.
Lemma lem3239411 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term118 _84925 s x.
Proof. exact (EQ_MP (@lem3239408 _84925 s x) (@lem3239312 _84925 s x h1)). Qed.
Lemma lem3239414 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (@lem3239411 _84925 s x h1 (@lem3239403 _84925 s x h2)). Qed.
Lemma lem3239415 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239414 _84925 s x h1 h2). Qed.
Lemma lem3239417 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239418 : term119 = False.
Proof. exact (@lem3239417 False). Qed.
Lemma lem3239419 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239418) (@lem3239415 _84925 s x h1 h2)). Qed.
Lemma lem3239421 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (proj2 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239422 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239421 _84925 s t P x h1). Qed.
Lemma lem3239424 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239425 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239424 (P x)). Qed.
Lemma lem3239426 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (EQ_MP (@lem3239425 _84925 P x) (@lem3239422 _84925 s t P x h1)). Qed.
Lemma lem3239429 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239431 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239429 (P x)). Qed.
Lemma lem3239434 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239431 _84925 P x) (@lem3239320 _84925 P x h1)). Qed.
Lemma lem3239437 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (@lem3239434 _84925 P x h1 (@lem3239426 _84925 s t P x h2)). Qed.
Lemma lem3239438 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239437 _84925 s t P x h1 h2). Qed.
Lemma lem3239440 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239441 : term119 = False.
Proof. exact (@lem3239440 False). Qed.
Lemma lem3239442 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239441) (@lem3239438 _84925 s t P x h1 h2)). Qed.
Lemma lem3239444 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3239445 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : term116 _84925 s x.
Proof. exact (fun h0 : term92 _84925 s x => @lem3239444 _84925 s x h1). Qed.
Lemma lem3239447 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239448 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term116 _84925 s x) = (s x).
Proof. exact (@lem3239447 (s x)). Qed.
Lemma lem3239449 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3239448 _84925 s x) (@lem3239445 _84925 s x h1)). Qed.
Lemma lem3239452 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239454 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term92 _84925 s x) = (term118 _84925 s x).
Proof. exact (@lem3239452 (s x)). Qed.
Lemma lem3239457 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) : term118 _84925 s x.
Proof. exact (EQ_MP (@lem3239454 _84925 s x) (@lem3239328 _84925 s x h1)). Qed.
Lemma lem3239460 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (@lem3239457 _84925 s x h1 (@lem3239449 _84925 s x h2)). Qed.
Lemma lem3239461 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239460 _84925 s x h1 h2). Qed.
Lemma lem3239463 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239464 : term119 = False.
Proof. exact (@lem3239463 False). Qed.
Lemma lem3239465 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239464) (@lem3239461 _84925 s x h1 h2)). Qed.
Lemma lem3239467 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (proj2 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239468 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239467 _84925 s t P x h1). Qed.
Lemma lem3239470 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239471 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239470 (P x)). Qed.
Lemma lem3239472 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (EQ_MP (@lem3239471 _84925 P x) (@lem3239468 _84925 s t P x h1)). Qed.
Lemma lem3239475 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239477 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239475 (P x)). Qed.
Lemma lem3239480 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239477 _84925 P x) (@lem3239334 _84925 P x h1)). Qed.
Lemma lem3239483 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (@lem3239480 _84925 P x h1 (@lem3239472 _84925 s t P x h2)). Qed.
Lemma lem3239484 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239483 _84925 s t P x h1 h2). Qed.
Lemma lem3239486 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239487 : term119 = False.
Proof. exact (@lem3239486 False). Qed.
Lemma lem3239488 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239487) (@lem3239484 _84925 s t P x h1 h2)). Qed.
Lemma lem3239490 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3239491 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : t x) : term116 _84925 t x.
Proof. exact (fun h0 : term92 _84925 t x => @lem3239490 _84925 t x h1). Qed.
Lemma lem3239493 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239494 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (term116 _84925 t x) = (t x).
Proof. exact (@lem3239493 (t x)). Qed.
Lemma lem3239495 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3239494 _84925 t x) (@lem3239491 _84925 t x h1)). Qed.
Lemma lem3239498 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239500 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (term92 _84925 t x) = (term118 _84925 t x).
Proof. exact (@lem3239498 (t x)). Qed.
Lemma lem3239503 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) : term118 _84925 t x.
Proof. exact (EQ_MP (@lem3239500 _84925 t x) (@lem3239342 _84925 t x h1)). Qed.
Lemma lem3239506 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (@lem3239503 _84925 t x h1 (@lem3239495 _84925 t x h2)). Qed.
Lemma lem3239507 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239506 _84925 t x h1 h2). Qed.
Lemma lem3239509 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239510 : term119 = False.
Proof. exact (@lem3239509 False). Qed.
Lemma lem3239511 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239510) (@lem3239507 _84925 t x h1 h2)). Qed.
Lemma lem3239513 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (proj2 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239514 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239513 _84925 s t P x h1). Qed.
Lemma lem3239516 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239517 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239516 (P x)). Qed.
Lemma lem3239518 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (EQ_MP (@lem3239517 _84925 P x) (@lem3239514 _84925 s t P x h1)). Qed.
Lemma lem3239521 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239523 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239521 (P x)). Qed.
Lemma lem3239526 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239523 _84925 P x) (@lem3239352 _84925 P x h1)). Qed.
Lemma lem3239529 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (@lem3239526 _84925 P x h1 (@lem3239518 _84925 s t P x h2)). Qed.
Lemma lem3239530 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239529 _84925 s t P x h1 h2). Qed.
Lemma lem3239532 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239533 : term119 = False.
Proof. exact (@lem3239532 False). Qed.
Lemma lem3239534 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239533) (@lem3239530 _84925 s t P x h1 h2)). Qed.
Lemma lem3239536 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (proj2 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239537 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239536 _84925 s t P x h1). Qed.
Lemma lem3239539 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239540 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239539 (P x)). Qed.
Lemma lem3239541 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (EQ_MP (@lem3239540 _84925 P x) (@lem3239537 _84925 s t P x h1)). Qed.
Lemma lem3239544 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239546 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239544 (P x)). Qed.
Lemma lem3239549 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239546 _84925 P x) (@lem3239358 _84925 P x h1)). Qed.
Lemma lem3239552 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (@lem3239549 _84925 P x h1 (@lem3239541 _84925 s t P x h2)). Qed.
Lemma lem3239553 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239552 _84925 s t P x h1 h2). Qed.
Lemma lem3239555 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239556 : term119 = False.
Proof. exact (@lem3239555 False). Qed.
Lemma lem3239557 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239556) (@lem3239553 _84925 s t P x h1 h2)). Qed.
Lemma lem3239559 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (proj2 (@lem3239086 _84925 s t P x h1)). Qed.
Lemma lem3239560 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239559 _84925 s t P x h1). Qed.
Lemma lem3239562 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239563 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239562 (P x)). Qed.
Lemma lem3239564 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : P x.
Proof. exact (EQ_MP (@lem3239563 _84925 P x) (@lem3239560 _84925 s t P x h1)). Qed.
Lemma lem3239567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239569 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239567 (P x)). Qed.
Lemma lem3239572 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239569 _84925 P x) (@lem3239366 _84925 P x h1)). Qed.
Lemma lem3239575 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (@lem3239572 _84925 P x h1 (@lem3239564 _84925 s t P x h2)). Qed.
Lemma lem3239576 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239575 _84925 s t P x h1 h2). Qed.
Lemma lem3239578 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239579 : term119 = False.
Proof. exact (@lem3239578 False). Qed.
Lemma lem3239580 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239579) (@lem3239576 _84925 s t P x h1 h2)). Qed.
Lemma lem3239582 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : s x.
Proof. exact (proj1 (@lem3239107 _84925 s P x h1)). Qed.
Lemma lem3239583 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : term116 _84925 s x.
Proof. exact (fun h0 : term92 _84925 s x => @lem3239582 _84925 s P x h1). Qed.
Lemma lem3239585 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239586 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term116 _84925 s x) = (s x).
Proof. exact (@lem3239585 (s x)). Qed.
Lemma lem3239587 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : s x.
Proof. exact (EQ_MP (@lem3239586 _84925 s x) (@lem3239583 _84925 s P x h1)). Qed.
Lemma lem3239590 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239592 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) : (term92 _84925 s x) = (term118 _84925 s x).
Proof. exact (@lem3239590 (s x)). Qed.
Lemma lem3239595 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term118 _84925 s x.
Proof. exact (EQ_MP (@lem3239592 _84925 s x) (@lem3239374 _84925 s t x h1)). Qed.
Lemma lem3239598 {_84925 : Type'} (t : _84925 -> Prop) (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 s P x) : False.
Proof. exact (@lem3239595 _84925 s t x h1 (@lem3239587 _84925 s P x h2)). Qed.
Lemma lem3239599 {_84925 : Type'} (t : _84925 -> Prop) (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 s P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239598 _84925 t s P x h1 h2). Qed.
Lemma lem3239601 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239602 : term119 = False.
Proof. exact (@lem3239601 False). Qed.
Lemma lem3239603 {_84925 : Type'} (t : _84925 -> Prop) (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 s P x) : False.
Proof. exact (EQ_MP (@lem3239602) (@lem3239599 _84925 t s P x h1 h2)). Qed.
Lemma lem3239605 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : P x.
Proof. exact (proj2 (@lem3239107 _84925 s P x h1)). Qed.
Lemma lem3239606 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239605 _84925 s P x h1). Qed.
Lemma lem3239608 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239609 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239608 (P x)). Qed.
Lemma lem3239610 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) : P x.
Proof. exact (EQ_MP (@lem3239609 _84925 P x) (@lem3239606 _84925 s P x h1)). Qed.
Lemma lem3239613 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239615 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239613 (P x)). Qed.
Lemma lem3239618 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239615 _84925 P x) (@lem3239382 _84925 P x h1)). Qed.
Lemma lem3239621 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : False.
Proof. exact (@lem3239618 _84925 P x h1 (@lem3239610 _84925 s P x h2)). Qed.
Lemma lem3239622 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239621 _84925 s P x h1 h2). Qed.
Lemma lem3239624 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239625 : term119 = False.
Proof. exact (@lem3239624 False). Qed.
Lemma lem3239626 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : False.
Proof. exact (EQ_MP (@lem3239625) (@lem3239622 _84925 s P x h1 h2)). Qed.
Lemma lem3239628 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : t x.
Proof. exact (proj1 (@lem3239108 _84925 t P x h1)). Qed.
Lemma lem3239629 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : term116 _84925 t x.
Proof. exact (fun h0 : term92 _84925 t x => @lem3239628 _84925 t P x h1). Qed.
Lemma lem3239631 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239632 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (term116 _84925 t x) = (t x).
Proof. exact (@lem3239631 (t x)). Qed.
Lemma lem3239633 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : t x.
Proof. exact (EQ_MP (@lem3239632 _84925 t x) (@lem3239629 _84925 t P x h1)). Qed.
Lemma lem3239636 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239638 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) : (term92 _84925 t x) = (term118 _84925 t x).
Proof. exact (@lem3239636 (t x)). Qed.
Lemma lem3239641 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) : term118 _84925 t x.
Proof. exact (EQ_MP (@lem3239638 _84925 t x) (@lem3239390 _84925 s t x h1)). Qed.
Lemma lem3239644 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 t P x) : False.
Proof. exact (@lem3239641 _84925 s t x h1 (@lem3239633 _84925 t P x h2)). Qed.
Lemma lem3239645 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239644 _84925 s t P x h1 h2). Qed.
Lemma lem3239647 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239648 : term119 = False.
Proof. exact (@lem3239647 False). Qed.
Lemma lem3239649 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term91 _84925 s t x) (h2 : term67 _84925 t P x) : False.
Proof. exact (EQ_MP (@lem3239648) (@lem3239645 _84925 s t P x h1 h2)). Qed.
Lemma lem3239651 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : P x.
Proof. exact (proj2 (@lem3239108 _84925 t P x h1)). Qed.
Lemma lem3239652 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : term116 _84925 P x.
Proof. exact (fun h0 : term92 _84925 P x => @lem3239651 _84925 t P x h1). Qed.
Lemma lem3239654 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239655 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term116 _84925 P x) = (P x).
Proof. exact (@lem3239654 (P x)). Qed.
Lemma lem3239656 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) : P x.
Proof. exact (EQ_MP (@lem3239655 _84925 P x) (@lem3239652 _84925 t P x h1)). Qed.
Lemma lem3239659 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3239661 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) : (term92 _84925 P x) = (term118 _84925 P x).
Proof. exact (@lem3239659 (P x)). Qed.
Lemma lem3239664 {_84925 : Type'} (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) : term118 _84925 P x.
Proof. exact (EQ_MP (@lem3239661 _84925 P x) (@lem3239396 _84925 P x h1)). Qed.
Lemma lem3239667 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : False.
Proof. exact (@lem3239664 _84925 P x h1 (@lem3239656 _84925 t P x h2)). Qed.
Lemma lem3239668 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : term119.
Proof. exact (fun h0 : ~ False => @lem3239667 _84925 t P x h1 h2). Qed.
Lemma lem3239670 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3239671 : term119 = False.
Proof. exact (@lem3239670 False). Qed.
Lemma lem3239672 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : False.
Proof. exact (EQ_MP (@lem3239671) (@lem3239668 _84925 t P x h1 h2)). Qed.
Lemma lem3239673 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239672 _84925 t P x h1 h2) (fun h3 : False => @lem3239396 _84925 P x h1)). Qed.
Lemma lem3239674 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : False.
Proof. exact (EQ_MP (@lem3239673 _84925 t P x h1 h2) (@lem3239396 _84925 P x h1)). Qed.
Lemma lem3239675 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239626 _84925 s P x h1 h2) (fun h3 : False => @lem3239382 _84925 P x h1)). Qed.
Lemma lem3239676 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : False.
Proof. exact (EQ_MP (@lem3239675 _84925 s P x h1 h2) (@lem3239382 _84925 P x h1)). Qed.
Lemma lem3239677 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239580 _84925 s t P x h1 h2) (fun h3 : False => @lem3239368 _84925 P x h1)). Qed.
Lemma lem3239678 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239677 _84925 s t P x h1 h2) (@lem3239368 _84925 P x h1)). Qed.
Lemma lem3239679 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239678 _84925 s t P x h1 h2) (fun h3 : False => @lem3239366 _84925 P x h1)). Qed.
Lemma lem3239680 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239679 _84925 s t P x h1 h2) (@lem3239366 _84925 P x h1)). Qed.
Lemma lem3239681 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239557 _84925 s t P x h1 h2) (fun h3 : False => @lem3239358 _84925 P x h1)). Qed.
Lemma lem3239682 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239681 _84925 s t P x h1 h2) (@lem3239358 _84925 P x h1)). Qed.
Lemma lem3239683 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239534 _84925 s t P x h1 h2) (fun h3 : False => @lem3239352 _84925 P x h1)). Qed.
Lemma lem3239684 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239683 _84925 s t P x h1 h2) (@lem3239352 _84925 P x h1)). Qed.
Lemma lem3239685 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (term92 _84925 t x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 t x => @lem3239511 _84925 t x h1 h2) (fun h3 : False => @lem3239342 _84925 t x h1)). Qed.
Lemma lem3239686 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239685 _84925 t x h1 h2) (@lem3239342 _84925 t x h1)). Qed.
Lemma lem3239687 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3239686 _84925 t x h1 h2) (fun h3 : False => @lem3239340 _84925 t x h2)). Qed.
Lemma lem3239688 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239687 _84925 t x h1 h2) (@lem3239340 _84925 t x h2)). Qed.
Lemma lem3239689 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239488 _84925 s t P x h1 h2) (fun h3 : False => @lem3239336 _84925 P x h1)). Qed.
Lemma lem3239690 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239689 _84925 s t P x h1 h2) (@lem3239336 _84925 P x h1)). Qed.
Lemma lem3239691 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239690 _84925 s t P x h1 h2) (fun h3 : False => @lem3239334 _84925 P x h1)). Qed.
Lemma lem3239692 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239691 _84925 s t P x h1 h2) (@lem3239334 _84925 P x h1)). Qed.
Lemma lem3239693 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239465 _84925 s x h1 h2) (fun h3 : False => @lem3239328 _84925 s x h1)). Qed.
Lemma lem3239694 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239693 _84925 s x h1 h2) (@lem3239328 _84925 s x h1)). Qed.
Lemma lem3239695 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239694 _84925 s x h1 h2) (fun h3 : False => @lem3239324 _84925 s x h2)). Qed.
Lemma lem3239696 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239695 _84925 s x h1 h2) (@lem3239324 _84925 s x h2)). Qed.
Lemma lem3239697 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239442 _84925 s t P x h1 h2) (fun h3 : False => @lem3239320 _84925 P x h1)). Qed.
Lemma lem3239698 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239697 _84925 s t P x h1 h2) (@lem3239320 _84925 P x h1)). Qed.
Lemma lem3239699 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239419 _84925 s x h1 h2) (fun h3 : False => @lem3239312 _84925 s x h1)). Qed.
Lemma lem3239700 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239699 _84925 s x h1 h2) (@lem3239312 _84925 s x h1)). Qed.
Lemma lem3239701 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239700 _84925 s x h1 h2) (fun h3 : False => @lem3239308 _84925 s x h2)). Qed.
Lemma lem3239702 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239701 _84925 s x h1 h2) (@lem3239308 _84925 s x h2)). Qed.
Lemma lem3239703 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239674 _84925 t P x h1 h2) (fun h3 : False => @lem3239304 _84925 P x h1)). Qed.
Lemma lem3239704 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : False.
Proof. exact (EQ_MP (@lem3239703 _84925 t P x h1 h2) (@lem3239304 _84925 P x h1)). Qed.
Lemma lem3239705 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239676 _84925 s P x h1 h2) (fun h3 : False => @lem3239276 _84925 P x h1)). Qed.
Lemma lem3239706 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : False.
Proof. exact (EQ_MP (@lem3239705 _84925 s P x h1 h2) (@lem3239276 _84925 P x h1)). Qed.
Lemma lem3239707 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239680 _84925 s t P x h1 h2) (fun h3 : False => @lem3239248 _84925 P x h1)). Qed.
Lemma lem3239708 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239707 _84925 s t P x h1 h2) (@lem3239248 _84925 P x h1)). Qed.
Lemma lem3239709 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239708 _84925 s t P x h1 h2) (fun h3 : False => @lem3239244 _84925 P x h1)). Qed.
Lemma lem3239710 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239709 _84925 s t P x h1 h2) (@lem3239244 _84925 P x h1)). Qed.
Lemma lem3239711 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239682 _84925 s t P x h1 h2) (fun h3 : False => @lem3239228 _84925 P x h1)). Qed.
Lemma lem3239712 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239711 _84925 s t P x h1 h2) (@lem3239228 _84925 P x h1)). Qed.
Lemma lem3239713 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239684 _84925 s t P x h1 h2) (fun h3 : False => @lem3239216 _84925 P x h1)). Qed.
Lemma lem3239714 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239713 _84925 s t P x h1 h2) (@lem3239216 _84925 P x h1)). Qed.
Lemma lem3239715 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (term92 _84925 t x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 t x => @lem3239688 _84925 t x h1 h2) (fun h3 : False => @lem3239196 _84925 t x h1)). Qed.
Lemma lem3239716 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239715 _84925 t x h1 h2) (@lem3239196 _84925 t x h1)). Qed.
Lemma lem3239717 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3239716 _84925 t x h1 h2) (fun h3 : False => @lem3239192 _84925 t x h2)). Qed.
Lemma lem3239718 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239717 _84925 t x h1 h2) (@lem3239192 _84925 t x h2)). Qed.
Lemma lem3239719 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239692 _84925 s t P x h1 h2) (fun h3 : False => @lem3239184 _84925 P x h1)). Qed.
Lemma lem3239720 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239719 _84925 s t P x h1 h2) (@lem3239184 _84925 P x h1)). Qed.
Lemma lem3239721 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239720 _84925 s t P x h1 h2) (fun h3 : False => @lem3239180 _84925 P x h1)). Qed.
Lemma lem3239722 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239721 _84925 s t P x h1 h2) (@lem3239180 _84925 P x h1)). Qed.
Lemma lem3239723 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239696 _84925 s x h1 h2) (fun h3 : False => @lem3239168 _84925 s x h1)). Qed.
Lemma lem3239724 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239723 _84925 s x h1 h2) (@lem3239168 _84925 s x h1)). Qed.
Lemma lem3239725 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239724 _84925 s x h1 h2) (fun h3 : False => @lem3239160 _84925 s x h2)). Qed.
Lemma lem3239726 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239725 _84925 s x h1 h2) (@lem3239160 _84925 s x h2)). Qed.
Lemma lem3239727 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239698 _84925 s t P x h1 h2) (fun h3 : False => @lem3239152 _84925 P x h1)). Qed.
Lemma lem3239728 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239727 _84925 s t P x h1 h2) (@lem3239152 _84925 P x h1)). Qed.
Lemma lem3239729 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239702 _84925 s x h1 h2) (fun h3 : False => @lem3239136 _84925 s x h1)). Qed.
Lemma lem3239730 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239729 _84925 s x h1 h2) (@lem3239136 _84925 s x h1)). Qed.
Lemma lem3239731 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239730 _84925 s x h1 h2) (fun h3 : False => @lem3239128 _84925 s x h2)). Qed.
Lemma lem3239732 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239731 _84925 s x h1 h2) (@lem3239128 _84925 s x h2)). Qed.
Lemma lem3239733 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239704 _84925 t P x h1 h2) (fun h3 : False => @lem3239304 _84925 P x h1)). Qed.
Lemma lem3239734 {_84925 : Type'} (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 t P x) : False.
Proof. exact (EQ_MP (@lem3239733 _84925 t P x h1 h2) (@lem3239304 _84925 P x h1)). Qed.
Lemma lem3239735 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239706 _84925 s P x h1 h2) (fun h3 : False => @lem3239276 _84925 P x h1)). Qed.
Lemma lem3239736 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term67 _84925 s P x) : False.
Proof. exact (EQ_MP (@lem3239735 _84925 s P x h1 h2) (@lem3239276 _84925 P x h1)). Qed.
Lemma lem3239737 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239710 _84925 s t P x h1 h2) (fun h3 : False => @lem3239248 _84925 P x h1)). Qed.
Lemma lem3239738 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239737 _84925 s t P x h1 h2) (@lem3239248 _84925 P x h1)). Qed.
Lemma lem3239739 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239738 _84925 s t P x h1 h2) (fun h3 : False => @lem3239244 _84925 P x h1)). Qed.
Lemma lem3239740 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239739 _84925 s t P x h1 h2) (@lem3239244 _84925 P x h1)). Qed.
Lemma lem3239741 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239712 _84925 s t P x h1 h2) (fun h3 : False => @lem3239228 _84925 P x h1)). Qed.
Lemma lem3239742 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239741 _84925 s t P x h1 h2) (@lem3239228 _84925 P x h1)). Qed.
Lemma lem3239743 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239714 _84925 s t P x h1 h2) (fun h3 : False => @lem3239216 _84925 P x h1)). Qed.
Lemma lem3239744 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239743 _84925 s t P x h1 h2) (@lem3239216 _84925 P x h1)). Qed.
Lemma lem3239745 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (term92 _84925 t x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 t x => @lem3239718 _84925 t x h1 h2) (fun h3 : False => @lem3239196 _84925 t x h1)). Qed.
Lemma lem3239746 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239745 _84925 t x h1 h2) (@lem3239196 _84925 t x h1)). Qed.
Lemma lem3239747 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3239746 _84925 t x h1 h2) (fun h3 : False => @lem3239192 _84925 t x h2)). Qed.
Lemma lem3239748 {_84925 : Type'} (t : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3239747 _84925 t x h1 h2) (@lem3239192 _84925 t x h2)). Qed.
Lemma lem3239749 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239722 _84925 s t P x h1 h2) (fun h3 : False => @lem3239184 _84925 P x h1)). Qed.
Lemma lem3239750 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239749 _84925 s t P x h1 h2) (@lem3239184 _84925 P x h1)). Qed.
Lemma lem3239751 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239750 _84925 s t P x h1 h2) (fun h3 : False => @lem3239180 _84925 P x h1)). Qed.
Lemma lem3239752 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239751 _84925 s t P x h1 h2) (@lem3239180 _84925 P x h1)). Qed.
Lemma lem3239753 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239726 _84925 s x h1 h2) (fun h3 : False => @lem3239168 _84925 s x h1)). Qed.
Lemma lem3239754 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239753 _84925 s x h1 h2) (@lem3239168 _84925 s x h1)). Qed.
Lemma lem3239755 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239754 _84925 s x h1 h2) (fun h3 : False => @lem3239160 _84925 s x h2)). Qed.
Lemma lem3239756 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239755 _84925 s x h1 h2) (@lem3239160 _84925 s x h2)). Qed.
Lemma lem3239757 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : (term92 _84925 P x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 P x => @lem3239728 _84925 s t P x h1 h2) (fun h3 : False => @lem3239152 _84925 P x h1)). Qed.
Lemma lem3239758 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239757 _84925 s t P x h1 h2) (@lem3239152 _84925 P x h1)). Qed.
Lemma lem3239759 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (term92 _84925 s x) = False.
Proof. exact (prop_ext (fun h3 : term92 _84925 s x => @lem3239732 _84925 s x h1 h2) (fun h3 : False => @lem3239136 _84925 s x h1)). Qed.
Lemma lem3239760 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239759 _84925 s x h1 h2) (@lem3239136 _84925 s x h1)). Qed.
Lemma lem3239761 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3239760 _84925 s x h1 h2) (fun h3 : False => @lem3239128 _84925 s x h2)). Qed.
Lemma lem3239762 {_84925 : Type'} (s : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3239761 _84925 s x h1 h2) (@lem3239128 _84925 s x h2)). Qed.
Lemma lem3239763 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 t P x) (h2 : term108 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239106 _84925 s t P x h2) (fun h0 : term91 _84925 s t x => @lem3239649 _84925 s t P x h0 h1) (fun h0 : term92 _84925 P x => @lem3239734 _84925 t P x h0 h1)). Qed.
Lemma lem3239764 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term67 _84925 s P x) (h2 : term108 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239106 _84925 s t P x h2) (fun h0 : term91 _84925 s t x => @lem3239603 _84925 t s P x h0 h1) (fun h0 : term92 _84925 P x => @lem3239736 _84925 s P x h0 h1)). Qed.
Lemma lem3239765 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term108 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239105 _84925 s t P x h1) (fun h0 : term67 _84925 s P x => @lem3239764 _84925 s t P x h0 h1) (fun h0 : term67 _84925 t P x => @lem3239763 _84925 s t P x h0 h1)). Qed.
Lemma lem3239766 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 P x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239088 _84925 s t P x h2) (fun h0 : term92 _84925 s x => @lem3239742 _84925 s t P x h1 h2) (fun h0 : term92 _84925 P x => @lem3239740 _84925 s t P x h1 h2)). Qed.
Lemma lem3239767 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term92 _84925 t x) (h2 : t x) (h3 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239088 _84925 s t P x h3) (fun h0 : term92 _84925 s x => @lem3239748 _84925 t x h1 h2) (fun h0 : term92 _84925 P x => @lem3239744 _84925 s t P x h0 h3)). Qed.
Lemma lem3239768 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : t x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239087 _84925 s t P x h2) (fun h0 : term92 _84925 t x => @lem3239767 _84925 s t P x h0 h1 h2) (fun h0 : term92 _84925 P x => @lem3239766 _84925 s t P x h0 h2)). Qed.
Lemma lem3239769 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : s x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239088 _84925 s t P x h2) (fun h0 : term92 _84925 s x => @lem3239756 _84925 s x h0 h1) (fun h0 : term92 _84925 P x => @lem3239752 _84925 s t P x h0 h2)). Qed.
Lemma lem3239770 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : s x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239088 _84925 s t P x h2) (fun h0 : term92 _84925 s x => @lem3239762 _84925 s x h0 h1) (fun h0 : term92 _84925 P x => @lem3239758 _84925 s t P x h0 h2)). Qed.
Lemma lem3239771 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : s x) (h2 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239087 _84925 s t P x h2) (fun h0 : term92 _84925 t x => @lem3239770 _84925 s t P x h1 h2) (fun h0 : term92 _84925 P x => @lem3239769 _84925 s t P x h1 h2)). Qed.
Lemma lem3239772 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term111 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239090 _84925 s t P x h1) (fun h0 : s x => @lem3239771 _84925 s t P x h0 h1) (fun h0 : t x => @lem3239768 _84925 s t P x h0 h1)). Qed.
Lemma lem3239773 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term89 _84925 s t P x) : False.
Proof. exact (or_elim (@lem3239082 _84925 s t P x h1) (fun h0 : term111 _84925 s t P x => @lem3239772 _84925 s t P x h0) (fun h0 : term108 _84925 s t P x => @lem3239765 _84925 s t P x h0)). Qed.
Lemma lem3239774 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term89 _84925 s t P x) : (term89 _84925 s t P x) = False.
Proof. exact (prop_ext (fun h2 : term89 _84925 s t P x => @lem3239773 _84925 s t P x h1) (fun h2 : False => @lem3238916 _84925 s t P x h1)). Qed.
Lemma lem3239775 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) (h1 : term89 _84925 s t P x) : False.
Proof. exact (EQ_MP (@lem3239774 _84925 s t P x h1) (@lem3238916 _84925 s t P x h1)). Qed.
Lemma lem3239776 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : term88 _84925 s t P x.
Proof. exact (fun h0 : term89 _84925 s t P x => @lem3239775 _84925 s t P x h0). Qed.
Lemma lem3239777 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) (x : _84925) : (term42 _84925 s t P x) = (term70 _84925 s t P x).
Proof. exact (EQ_MP (@lem3238915 _84925 s t P x) (@lem3239776 _84925 s t P x)). Qed.
Lemma lem3239782 {_84925 : Type'} (s : _84925 -> Prop) (t : _84925 -> Prop) (P : _84925 -> Prop) : term73 _84925 s t P.
Proof. exact (fun x : _84925 => @lem3239777 _84925 s t P x). Qed.
Lemma lem3239787 {_84925 : Type'} (s : _84925 -> Prop) (P : _84925 -> Prop) : term75 _84925 s P.
Proof. exact (fun t : _84925 -> Prop => @lem3239782 _84925 s t P). Qed.
Lemma lem3239792 {_84925 : Type'} (P : _84925 -> Prop) : term77 _84925 P.
Proof. exact (fun s : _84925 -> Prop => @lem3239787 _84925 s P). Qed.
Lemma lem3239797 {_84925 : Type'} : term79 _84925.
Proof. exact (fun P : _84925 -> Prop => @lem3239792 _84925 P). Qed.
Lemma lem3239798 {_84925 : Type'} : term81 _84925.
Proof. exact (EQ_MP (@lem3238911 _84925) (@lem3239797 _84925)). Qed.
Lemma lem3239800 {_84925 : Type'} : term81 _84925.
Proof. exact (@lem3238799 _84925 (@lem3239798 _84925)). Qed.
Lemma lem3239801 {_84925 : Type'} (h1 : term82 _84925) : False.
Proof. exact (@lem3239800 _84925 (@lem3238783 _84925 h1)). Qed.
Lemma lem3239802 {_84925 : Type'} (h1 : term82 _84925) : (term82 _84925) = False.
Proof. exact (prop_ext (fun h2 : term82 _84925 => @lem3239801 _84925 h1) (fun h2 : False => @lem3238783 _84925 h1)). Qed.
Lemma lem3239803 {_84925 : Type'} (h1 : term82 _84925) : False.
Proof. exact (EQ_MP (@lem3239802 _84925 h1) (@lem3238783 _84925 h1)). Qed.
Lemma lem3239804 {_84925 : Type'} : term81 _84925.
Proof. exact (fun h0 : term82 _84925 => @lem3239803 _84925 h0). Qed.
Lemma lem3239805 {_84925 : Type'} : term79 _84925.
Proof. exact (EQ_MP (@lem3238782 _84925) (@lem3239804 _84925)). Qed.
Lemma lem3239806 {_84925 : Type'} : term15 _84925.
Proof. exact (EQ_MP (@lem3238778 _84925) (@lem3239805 _84925)). Qed.
Lemma lem3239807 {_84925 : Type'} : term14 _84925.
Proof. exact (EQ_MP (@lem3238594 _84925) (@lem3239806 _84925)). Qed.
