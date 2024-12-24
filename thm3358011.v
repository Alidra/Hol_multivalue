Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3358011_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Lemma lem3356599 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3356600 {_87274 : Type'} (s : type686 _87274) (x : _87274) : (term0 _87274 x s) = (term1 _87274 s x).
Proof. exact (@lem3356599 _87274 s x). Qed.
Lemma lem3356601 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term2 _87274 x s u) = (term3 _87274 s u x).
Proof. exact (@lem3356600 _87274 (@INSERT (_87274 -> Prop) s u) x). Qed.
Lemma lem3356609 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A x y s) = (term5 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3356610 {_87274 : Type'} (y : _87274 -> Prop) (x : _87274 -> Prop) (s : type686 _87274) : (term6 _87274 x y s) = (term7 _87274 y x s).
Proof. exact (@lem3356609 (_87274 -> Prop) y x s). Qed.
Lemma lem3356611 {_87274 : Type'} (s : _87274 -> Prop) (t : _87274 -> Prop) (u : type686 _87274) : (term6 _87274 t s u) = (term7 _87274 s t u).
Proof. exact (@lem3356610 _87274 s t u). Qed.
Lemma lem3356617 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3356618 {_87274 : Type'} (P : type686 _87274) (x : _87274 -> Prop) : (@IN (_87274 -> Prop) x P) = (P x).
Proof. exact (@lem3356617 (_87274 -> Prop) P x). Qed.
Lemma lem3356619 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (@IN (_87274 -> Prop) t u) = (u t).
Proof. exact (@lem3356618 _87274 u t). Qed.
Lemma lem3356620 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) : (term8 _87274 t s) = (term8 _87274 t s).
Proof. exact (eq_refl (term8 _87274 t s)). Qed.
Lemma lem3356621 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term7 _87274 s t u) = (term9 _87274 s u t).
Proof. exact (MK_COMB (@lem3356620 _87274 t s) (@lem3356619 _87274 u t)). Qed.
Lemma lem3356624 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term6 _87274 t s u) = (term9 _87274 s u t).
Proof. exact (TRANS (@lem3356611 _87274 s t u) (@lem3356621 _87274 s u t)). Qed.
Lemma lem3356625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3356626 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term10 _87274 t s u) = (term11 _87274 s u t).
Proof. exact (MK_COMB (@lem3356625) (@lem3356624 _87274 s u t)). Qed.
Lemma lem3356628 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3356629 {_87274 : Type'} (P : _87274 -> Prop) (x : _87274) : (@IN _87274 x P) = (P x).
Proof. exact (@lem3356628 _87274 P x). Qed.
Lemma lem3356630 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (@IN _87274 x t) = (t x).
Proof. exact (@lem3356629 _87274 t x). Qed.
Lemma lem3356631 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term12 _87274 s u x t) = (term13 _87274 s u t x).
Proof. exact (MK_COMB (@lem3356626 _87274 s u t) (@lem3356630 _87274 t x)). Qed.
Lemma lem3356634 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term14 _87274 s u x) = (term15 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356631 _87274 s u t x)). Qed.
Lemma lem3356635 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356636 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term3 _87274 s u x) = (term16 _87274 s u x).
Proof. exact (MK_COMB (@lem3356635 _87274) (@lem3356634 _87274 s u x)). Qed.
Lemma lem3356641 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term2 _87274 x s u) = (term16 _87274 s u x).
Proof. exact (TRANS (@lem3356601 _87274 s u x) (@lem3356636 _87274 s u x)). Qed.
Lemma lem3356642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356643 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term17 _87274 x s u) = (term18 _87274 s u x).
Proof. exact (MK_COMB (@lem3356642) (@lem3356641 _87274 s u x)). Qed.
Lemma lem3356645 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term19 A x s t) = (term20 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3356646 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (t : _87274 -> Prop) : (term19 _87274 x s t) = (term20 _87274 s x t).
Proof. exact (@lem3356645 _87274 s x t). Qed.
Lemma lem3356647 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) : (term21 _87274 x s u) = (term22 _87274 s x u).
Proof. exact (@lem3356646 _87274 s x (@INTERS _87274 u)). Qed.
Lemma lem3356651 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3356652 {_87274 : Type'} (P : _87274 -> Prop) (x : _87274) : (@IN _87274 x P) = (P x).
Proof. exact (@lem3356651 _87274 P x). Qed.
Lemma lem3356653 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (@IN _87274 x s) = (s x).
Proof. exact (@lem3356652 _87274 s x). Qed.
Lemma lem3356654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3356655 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term23 _87274 x s) = (term24 _87274 s x).
Proof. exact (MK_COMB (@lem3356654) (@lem3356653 _87274 s x)). Qed.
Lemma lem3356657 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3356658 {_87274 : Type'} (s : type686 _87274) (x : _87274) : (term0 _87274 x s) = (term1 _87274 s x).
Proof. exact (@lem3356657 _87274 s x). Qed.
Lemma lem3356659 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term0 _87274 x u) = (term1 _87274 u x).
Proof. exact (@lem3356658 _87274 u x). Qed.
Lemma lem3356667 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3356668 {_87274 : Type'} (P : type686 _87274) (x : _87274 -> Prop) : (@IN (_87274 -> Prop) x P) = (P x).
Proof. exact (@lem3356667 (_87274 -> Prop) P x). Qed.
Lemma lem3356669 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (@IN (_87274 -> Prop) t u) = (u t).
Proof. exact (@lem3356668 _87274 u t). Qed.
Lemma lem3356670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3356671 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term25 _87274 t u) = (term26 _87274 u t).
Proof. exact (MK_COMB (@lem3356670) (@lem3356669 _87274 u t)). Qed.
Lemma lem3356673 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3356674 {_87274 : Type'} (P : _87274 -> Prop) (x : _87274) : (@IN _87274 x P) = (P x).
Proof. exact (@lem3356673 _87274 P x). Qed.
Lemma lem3356675 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (@IN _87274 x t) = (t x).
Proof. exact (@lem3356674 _87274 t x). Qed.
Lemma lem3356676 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term27 _87274 u x t) = (term28 _87274 u t x).
Proof. exact (MK_COMB (@lem3356671 _87274 u t) (@lem3356675 _87274 t x)). Qed.
Lemma lem3356679 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term29 _87274 u x) = (term30 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356676 _87274 u t x)). Qed.
Lemma lem3356680 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356681 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term1 _87274 u x) = (term31 _87274 u x).
Proof. exact (MK_COMB (@lem3356680 _87274) (@lem3356679 _87274 u x)). Qed.
Lemma lem3356686 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term0 _87274 x u) = (term31 _87274 u x).
Proof. exact (TRANS (@lem3356659 _87274 u x) (@lem3356681 _87274 u x)). Qed.
Lemma lem3356687 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term22 _87274 s x u) = (term32 _87274 s u x).
Proof. exact (MK_COMB (@lem3356655 _87274 s x) (@lem3356686 _87274 u x)). Qed.
Lemma lem3356690 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term21 _87274 x s u) = (term32 _87274 s u x).
Proof. exact (TRANS (@lem3356647 _87274 s x u) (@lem3356687 _87274 s u x)). Qed.
Lemma lem3356691 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term2 _87274 x s u) = (term21 _87274 x s u)) = ((term16 _87274 s u x) = (term32 _87274 s u x)).
Proof. exact (MK_COMB (@lem3356643 _87274 s u x) (@lem3356690 _87274 s u x)). Qed.
Lemma lem3356694 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term33 _87274 s u) = (term34 _87274 s u).
Proof. exact (fun_ext (fun x : _87274 => @lem3356691 _87274 s u x)). Qed.
Lemma lem3356695 {_87274 : Type'} : (@all _87274) = (@all _87274).
Proof. exact (eq_refl (@all _87274)). Qed.
Lemma lem3356696 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term35 _87274 s u) = (term36 _87274 s u).
Proof. exact (MK_COMB (@lem3356695 _87274) (@lem3356694 _87274 s u)). Qed.
Lemma lem3356701 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term36 _87274 s u) = (term35 _87274 s u).
Proof. exact (SYM (@lem3356696 _87274 s u)). Qed.
Lemma lem3356703 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3356704 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term36 _87274 s u) = (term38 _87274 s u).
Proof. exact (@lem3356703 (term36 _87274 s u)). Qed.
Lemma lem3356705 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term38 _87274 s u) = (term36 _87274 s u).
Proof. exact (SYM (@lem3356704 _87274 s u)). Qed.
Lemma lem3356706 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term39 _87274 s u) : term39 _87274 s u.
Proof. exact (h1). Qed.
Lemma lem3356709 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term38 _87274 s u) : term38 _87274 s u.
Proof. exact (h1). Qed.
Lemma lem3356710 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term40 _87274 s u.
Proof. exact (fun h0 : term38 _87274 s u => @lem3356709 _87274 s u h0). Qed.
Lemma lem3356711 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term40 _87274 s u) : term40 _87274 s u.
Proof. exact (h1). Qed.
Lemma lem3356712 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term38 _87274 s u) : term38 _87274 s u.
Proof. exact (h1). Qed.
Lemma lem3356713 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term38 _87274 s u) (h2 : term40 _87274 s u) : term38 _87274 s u.
Proof. exact (@lem3356711 _87274 s u h2 (@lem3356712 _87274 s u h1)). Qed.
Lemma lem3356714 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term38 _87274 s u) : term41 _87274 s u.
Proof. exact (fun h0 : term40 _87274 s u => @lem3356713 _87274 s u h1 h0). Qed.
Lemma lem3356715 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term40 _87274 s u) : term40 _87274 s u.
Proof. exact (h1). Qed.
Lemma lem3356716 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term38 _87274 s u) (h2 : term40 _87274 s u) : term38 _87274 s u.
Proof. exact (@lem3356714 _87274 s u h1 (@lem3356715 _87274 s u h2)). Qed.
Lemma lem3356717 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term40 _87274 s u) : term40 _87274 s u.
Proof. exact (fun h0 : term38 _87274 s u => @lem3356716 _87274 s u h0 h1). Qed.
Lemma lem3356718 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term42 _87274 s u.
Proof. exact (fun h0 : term40 _87274 s u => @lem3356717 _87274 s u h0). Qed.
Lemma lem3356721 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term40 _87274 s u.
Proof. exact (@lem3356718 _87274 s u (@lem3356710 _87274 s u)). Qed.
Lemma lem3356722 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term40 _87274 s u.
Proof. exact (@lem3356721 _87274 s u). Qed.
Lemma lem3356732 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3356733 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term38 _87274 s u) = (term43 _87274 s u).
Proof. exact (@lem3356732 (term39 _87274 s u)). Qed.
Lemma lem3356735 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3356736 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term43 _87274 s u) = (term36 _87274 s u).
Proof. exact (@lem3356735 (term36 _87274 s u)). Qed.
Lemma lem3356741 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term38 _87274 s u) = (term36 _87274 s u).
Proof. exact (TRANS (@lem3356733 _87274 s u) (@lem3356736 _87274 s u)). Qed.
Lemma lem3356758 {_87274 : Type'} (u : type686 _87274) : (term45 _87274 u) = (term46 _87274 u).
Proof. exact (fun_ext (fun s : _87274 -> Prop => @lem3356741 _87274 s u)). Qed.
Lemma lem3356759 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356760 {_87274 : Type'} (u : type686 _87274) : (term47 _87274 u) = (term48 _87274 u).
Proof. exact (MK_COMB (@lem3356759 _87274) (@lem3356758 _87274 u)). Qed.
Lemma lem3356765 {_87274 : Type'} : (term49 _87274) = (term50 _87274).
Proof. exact (fun_ext (fun u : type686 _87274 => @lem3356760 _87274 u)). Qed.
Lemma lem3356766 {_87274 : Type'} : (@all ((_87274 -> Prop) -> Prop)) = (@all ((_87274 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87274 -> Prop) -> Prop))). Qed.
Lemma lem3356775 {_87274 : Type'} : (term51 _87274) = (term52 _87274).
Proof. exact (MK_COMB (@lem3356766 _87274) (@lem3356765 _87274)). Qed.
Lemma lem3356780 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term28 _87274 u t x) = (term28 _87274 u t x).
Proof. exact (eq_refl (term28 _87274 u t x)). Qed.
Lemma lem3356781 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term30 _87274 u x) = (term30 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356780 _87274 u t x)). Qed.
Lemma lem3356782 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356783 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term31 _87274 u x) = (term31 _87274 u x).
Proof. exact (MK_COMB (@lem3356782 _87274) (@lem3356781 _87274 u x)). Qed.
Lemma lem3356786 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term24 _87274 s x) = (term24 _87274 s x).
Proof. exact (eq_refl (term24 _87274 s x)). Qed.
Lemma lem3356787 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term32 _87274 s u x) = (term32 _87274 s u x).
Proof. exact (MK_COMB (@lem3356786 _87274 s x) (@lem3356783 _87274 u x)). Qed.
Lemma lem3356796 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term13 _87274 s u t x) = (term13 _87274 s u t x).
Proof. exact (eq_refl (term13 _87274 s u t x)). Qed.
Lemma lem3356797 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term15 _87274 s u x) = (term15 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356796 _87274 s u t x)). Qed.
Lemma lem3356798 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356799 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term16 _87274 s u x) = (term16 _87274 s u x).
Proof. exact (MK_COMB (@lem3356798 _87274) (@lem3356797 _87274 s u x)). Qed.
Lemma lem3356800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356801 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term18 _87274 s u x) = (term18 _87274 s u x).
Proof. exact (MK_COMB (@lem3356800) (@lem3356799 _87274 s u x)). Qed.
Lemma lem3356802 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term16 _87274 s u x) = (term32 _87274 s u x)) = ((term16 _87274 s u x) = (term32 _87274 s u x)).
Proof. exact (MK_COMB (@lem3356801 _87274 s u x) (@lem3356787 _87274 s u x)). Qed.
Lemma lem3356803 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term34 _87274 s u) = (term34 _87274 s u).
Proof. exact (fun_ext (fun x : _87274 => @lem3356802 _87274 s u x)). Qed.
Lemma lem3356804 {_87274 : Type'} : (@all _87274) = (@all _87274).
Proof. exact (eq_refl (@all _87274)). Qed.
Lemma lem3356805 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term36 _87274 s u) = (term36 _87274 s u).
Proof. exact (MK_COMB (@lem3356804 _87274) (@lem3356803 _87274 s u)). Qed.
Lemma lem3356806 {_87274 : Type'} (u : type686 _87274) : (term46 _87274 u) = (term46 _87274 u).
Proof. exact (fun_ext (fun s : _87274 -> Prop => @lem3356805 _87274 s u)). Qed.
Lemma lem3356807 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356808 {_87274 : Type'} (u : type686 _87274) : (term48 _87274 u) = (term48 _87274 u).
Proof. exact (MK_COMB (@lem3356807 _87274) (@lem3356806 _87274 u)). Qed.
Lemma lem3356809 {_87274 : Type'} : (term50 _87274) = (term50 _87274).
Proof. exact (fun_ext (fun u : type686 _87274 => @lem3356808 _87274 u)). Qed.
Lemma lem3356810 {_87274 : Type'} : (@all ((_87274 -> Prop) -> Prop)) = (@all ((_87274 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87274 -> Prop) -> Prop))). Qed.
Lemma lem3356811 {_87274 : Type'} : (term52 _87274) = (term52 _87274).
Proof. exact (MK_COMB (@lem3356810 _87274) (@lem3356809 _87274)). Qed.
Lemma lem3356852 {_87274 : Type'} : (term51 _87274) = (term52 _87274).
Proof. exact (TRANS (@lem3356775 _87274) (@lem3356811 _87274)). Qed.
Lemma lem3356853 {_87274 : Type'} : (term52 _87274) = (term51 _87274).
Proof. exact (SYM (@lem3356852 _87274)). Qed.
Lemma lem3356855 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3356856 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term16 _87274 s u x) = (term32 _87274 s u x)) = (term53 _87274 s u x).
Proof. exact (@lem3356855 ((term16 _87274 s u x) = (term32 _87274 s u x))). Qed.
Lemma lem3356857 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term53 _87274 s u x) = ((term16 _87274 s u x) = (term32 _87274 s u x)).
Proof. exact (SYM (@lem3356856 _87274 s u x)). Qed.
Lemma lem3356858 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term54 _87274 s u x) : term54 _87274 s u x.
Proof. exact (h1). Qed.
Lemma lem3356867 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term55 _87274 s u t) = (term56 _87274 s u t).
Proof. exact (@lem17160 (t = s) (u t)). Qed.
Lemma lem3356872 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3356877 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term57 _87274 s u t x) = (term58 _87274 s u t x).
Proof. exact (@lem17362 (term9 _87274 s u t) (t x)). Qed.
Lemma lem3356878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3356879 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term59 _87274 s u t) = (term60 _87274 s u t).
Proof. exact (MK_COMB (@lem3356878) (@lem3356867 _87274 s u t)). Qed.
Lemma lem3356880 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term61 _87274 s u t x) = (term62 _87274 s u t x).
Proof. exact (MK_COMB (@lem3356879 _87274 s u t) (@lem3356872 _87274 t x)). Qed.
Lemma lem3356881 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term13 _87274 s u t x) = (term61 _87274 s u t x).
Proof. exact (@lem17265 (term9 _87274 s u t) (t x)). Qed.
Lemma lem3356882 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term13 _87274 s u t x) = (term62 _87274 s u t x).
Proof. exact (TRANS (@lem3356881 _87274 s u t x) (@lem3356880 _87274 s u t x)). Qed.
Lemma lem3356883 {_87274 : Type'} (P : type686 _87274) : (term63 _87274 P) = (term64 _87274 P).
Proof. exact (@lem18392 (_87274 -> Prop) P). Qed.
Lemma lem3356884 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term65 _87274 s u x) = (term66 _87274 s u x).
Proof. exact (@lem3356883 _87274 (term15 _87274 s u x)). Qed.
Lemma lem3356885 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term67 _87274 s u x t) = (term13 _87274 s u t x).
Proof. exact (eq_refl (term67 _87274 s u x t)). Qed.
Lemma lem3356886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3356887 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term68 _87274 s u x t) = (term57 _87274 s u t x).
Proof. exact (MK_COMB (@lem3356886) (@lem3356885 _87274 s u t x)). Qed.
Lemma lem3356888 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term68 _87274 s u x t) = (term58 _87274 s u t x).
Proof. exact (TRANS (@lem3356887 _87274 s u t x) (@lem3356877 _87274 s u t x)). Qed.
Lemma lem3356889 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term69 _87274 s u x) = (term70 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356888 _87274 s u t x)). Qed.
Lemma lem3356890 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3356891 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term66 _87274 s u x) = (term71 _87274 s u x).
Proof. exact (MK_COMB (@lem3356890 _87274) (@lem3356889 _87274 s u x)). Qed.
Lemma lem3356892 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term65 _87274 s u x) = (term71 _87274 s u x).
Proof. exact (TRANS (@lem3356884 _87274 s u x) (@lem3356891 _87274 s u x)). Qed.
Lemma lem3356893 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term15 _87274 s u x) = (term72 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356882 _87274 s u t x)). Qed.
Lemma lem3356894 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356895 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term16 _87274 s u x) = (term73 _87274 s u x).
Proof. exact (MK_COMB (@lem3356894 _87274) (@lem3356893 _87274 s u x)). Qed.
Lemma lem3356906 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term74 _87274 u t x) = (term75 _87274 u t x).
Proof. exact (@lem17362 (u t) (t x)). Qed.
Lemma lem3356911 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term28 _87274 u t x) = (term76 _87274 u t x).
Proof. exact (@lem17265 (u t) (t x)). Qed.
Lemma lem3356912 {_87274 : Type'} (P : type686 _87274) : (term63 _87274 P) = (term64 _87274 P).
Proof. exact (@lem18392 (_87274 -> Prop) P). Qed.
Lemma lem3356913 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term77 _87274 u x) = (term78 _87274 u x).
Proof. exact (@lem3356912 _87274 (term30 _87274 u x)). Qed.
Lemma lem3356914 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term79 _87274 u x t) = (term28 _87274 u t x).
Proof. exact (eq_refl (term79 _87274 u x t)). Qed.
Lemma lem3356915 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3356916 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term80 _87274 u x t) = (term74 _87274 u t x).
Proof. exact (MK_COMB (@lem3356915) (@lem3356914 _87274 u t x)). Qed.
Lemma lem3356917 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term80 _87274 u x t) = (term75 _87274 u t x).
Proof. exact (TRANS (@lem3356916 _87274 u t x) (@lem3356906 _87274 u t x)). Qed.
Lemma lem3356918 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term81 _87274 u x) = (term82 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356917 _87274 u t x)). Qed.
Lemma lem3356919 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3356920 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term78 _87274 u x) = (term83 _87274 u x).
Proof. exact (MK_COMB (@lem3356919 _87274) (@lem3356918 _87274 u x)). Qed.
Lemma lem3356921 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term77 _87274 u x) = (term83 _87274 u x).
Proof. exact (TRANS (@lem3356913 _87274 u x) (@lem3356920 _87274 u x)). Qed.
Lemma lem3356922 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term30 _87274 u x) = (term84 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3356911 _87274 u t x)). Qed.
Lemma lem3356923 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3356924 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term31 _87274 u x) = (term85 _87274 u x).
Proof. exact (MK_COMB (@lem3356923 _87274) (@lem3356922 _87274 u x)). Qed.
Lemma lem3356926 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term86 _87274 s x) = (term86 _87274 s x).
Proof. exact (eq_refl (term86 _87274 s x)). Qed.
Lemma lem3356927 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term87 _87274 s u x) = (term88 _87274 s u x).
Proof. exact (MK_COMB (@lem3356926 _87274 s x) (@lem3356921 _87274 u x)). Qed.
Lemma lem3356928 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term89 _87274 s u x) = (term87 _87274 s u x).
Proof. exact (@lem17045 (s x) (term31 _87274 u x)). Qed.
Lemma lem3356929 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term89 _87274 s u x) = (term88 _87274 s u x).
Proof. exact (TRANS (@lem3356928 _87274 s u x) (@lem3356927 _87274 s u x)). Qed.
Lemma lem3356931 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term24 _87274 s x) = (term24 _87274 s x).
Proof. exact (eq_refl (term24 _87274 s x)). Qed.
Lemma lem3356932 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term32 _87274 s u x) = (term90 _87274 s u x).
Proof. exact (MK_COMB (@lem3356931 _87274 s x) (@lem3356924 _87274 u x)). Qed.
Lemma lem3356933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3356934 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term91 _87274 s u x) = (term92 _87274 s u x).
Proof. exact (MK_COMB (@lem3356933) (@lem3356892 _87274 s u x)). Qed.
Lemma lem3356935 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term93 _87274 s u x) = (term94 _87274 s u x).
Proof. exact (MK_COMB (@lem3356934 _87274 s u x) (@lem3356932 _87274 s u x)). Qed.
Lemma lem3356936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3356937 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term95 _87274 s u x) = (term96 _87274 s u x).
Proof. exact (MK_COMB (@lem3356936) (@lem3356895 _87274 s u x)). Qed.
Lemma lem3356938 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term97 _87274 s u x) = (term98 _87274 s u x).
Proof. exact (MK_COMB (@lem3356937 _87274 s u x) (@lem3356929 _87274 s u x)). Qed.
Lemma lem3356939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3356940 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term99 _87274 s u x) = (term100 _87274 s u x).
Proof. exact (MK_COMB (@lem3356939) (@lem3356938 _87274 s u x)). Qed.
Lemma lem3356941 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term101 _87274 s u x) = (term102 _87274 s u x).
Proof. exact (MK_COMB (@lem3356940 _87274 s u x) (@lem3356935 _87274 s u x)). Qed.
Lemma lem3356942 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term54 _87274 s u x) = (term101 _87274 s u x).
Proof. exact (@lem17646 (term16 _87274 s u x) (term32 _87274 s u x)). Qed.
Lemma lem3356943 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term54 _87274 s u x) = (term102 _87274 s u x).
Proof. exact (TRANS (@lem3356942 _87274 s u x) (@lem3356941 _87274 s u x)). Qed.
Lemma lem3357118 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3357119 {_87274 : Type'} (P : Prop) (Q : type686 _87274) : (term105 _87274 P Q) = (term106 _87274 P Q).
Proof. exact (@lem3357118 (_87274 -> Prop) P Q). Qed.
Lemma lem3357120 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term107 _87274 s u x) = (term108 _87274 s u x).
Proof. exact (@lem3357119 _87274 (term109 _87274 s x) (term82 _87274 u x)). Qed.
Lemma lem3357121 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term110 _87274 u x t) = (term75 _87274 u t x).
Proof. exact (eq_refl (term110 _87274 u x t)). Qed.
Lemma lem3357122 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term111 _87274 u x) = (term82 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357121 _87274 u t x)). Qed.
Lemma lem3357123 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357124 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term112 _87274 u x) = (term83 _87274 u x).
Proof. exact (MK_COMB (@lem3357123 _87274) (@lem3357122 _87274 u x)). Qed.
Lemma lem3357125 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term86 _87274 s x) = (term86 _87274 s x).
Proof. exact (eq_refl (term86 _87274 s x)). Qed.
Lemma lem3357126 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term107 _87274 s u x) = (term88 _87274 s u x).
Proof. exact (MK_COMB (@lem3357125 _87274 s x) (@lem3357124 _87274 u x)). Qed.
Lemma lem3357127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357128 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term113 _87274 s u x) = (term114 _87274 s u x).
Proof. exact (MK_COMB (@lem3357127) (@lem3357126 _87274 s u x)). Qed.
Lemma lem3357129 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term110 _87274 u x t) = (term75 _87274 u t x).
Proof. exact (eq_refl (term110 _87274 u x t)). Qed.
Lemma lem3357130 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term86 _87274 s x) = (term86 _87274 s x).
Proof. exact (eq_refl (term86 _87274 s x)). Qed.
Lemma lem3357131 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term115 _87274 s u x t) = (term116 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357130 _87274 s x) (@lem3357129 _87274 u t x)). Qed.
Lemma lem3357132 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term117 _87274 s u x) = (term118 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357131 _87274 s u t x)). Qed.
Lemma lem3357133 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357134 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term108 _87274 s u x) = (term119 _87274 s u x).
Proof. exact (MK_COMB (@lem3357133 _87274) (@lem3357132 _87274 s u x)). Qed.
Lemma lem3357135 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term107 _87274 s u x) = (term108 _87274 s u x)) = ((term88 _87274 s u x) = (term119 _87274 s u x)).
Proof. exact (MK_COMB (@lem3357128 _87274 s u x) (@lem3357134 _87274 s u x)). Qed.
Lemma lem3357136 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term88 _87274 s u x) = (term119 _87274 s u x).
Proof. exact (EQ_MP (@lem3357135 _87274 s u x) (@lem3357120 _87274 s u x)). Qed.
Lemma lem3357137 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term96 _87274 s u x) = (term96 _87274 s u x).
Proof. exact (eq_refl (term96 _87274 s u x)). Qed.
Lemma lem3357138 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term98 _87274 s u x) = (term120 _87274 s u x).
Proof. exact (MK_COMB (@lem3357137 _87274 s u x) (@lem3357136 _87274 s u x)). Qed.
Lemma lem3357140 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3357141 {_87274 : Type'} (P : Prop) (Q : type686 _87274) : (term123 _87274 P Q) = (term124 _87274 P Q).
Proof. exact (@lem3357140 (_87274 -> Prop) P Q). Qed.
Lemma lem3357142 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term125 _87274 s u x) = (term126 _87274 s u x).
Proof. exact (@lem3357141 _87274 (term73 _87274 s u x) (term118 _87274 s u x)). Qed.
Lemma lem3357143 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term127 _87274 s u x t) = (term116 _87274 s u t x).
Proof. exact (eq_refl (term127 _87274 s u x t)). Qed.
Lemma lem3357144 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term128 _87274 s u x) = (term118 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357143 _87274 s u t x)). Qed.
Lemma lem3357145 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357146 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term129 _87274 s u x) = (term119 _87274 s u x).
Proof. exact (MK_COMB (@lem3357145 _87274) (@lem3357144 _87274 s u x)). Qed.
Lemma lem3357147 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term96 _87274 s u x) = (term96 _87274 s u x).
Proof. exact (eq_refl (term96 _87274 s u x)). Qed.
Lemma lem3357148 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term125 _87274 s u x) = (term120 _87274 s u x).
Proof. exact (MK_COMB (@lem3357147 _87274 s u x) (@lem3357146 _87274 s u x)). Qed.
Lemma lem3357149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357150 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term130 _87274 s u x) = (term131 _87274 s u x).
Proof. exact (MK_COMB (@lem3357149) (@lem3357148 _87274 s u x)). Qed.
Lemma lem3357151 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term127 _87274 s u x t) = (term116 _87274 s u t x).
Proof. exact (eq_refl (term127 _87274 s u x t)). Qed.
Lemma lem3357152 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term96 _87274 s u x) = (term96 _87274 s u x).
Proof. exact (eq_refl (term96 _87274 s u x)). Qed.
Lemma lem3357153 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term132 _87274 s u x t) = (term133 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357152 _87274 s u x) (@lem3357151 _87274 s u t x)). Qed.
Lemma lem3357154 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term134 _87274 s u x) = (term135 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357153 _87274 s u t x)). Qed.
Lemma lem3357155 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357156 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term126 _87274 s u x) = (term136 _87274 s u x).
Proof. exact (MK_COMB (@lem3357155 _87274) (@lem3357154 _87274 s u x)). Qed.
Lemma lem3357157 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term125 _87274 s u x) = (term126 _87274 s u x)) = ((term120 _87274 s u x) = (term136 _87274 s u x)).
Proof. exact (MK_COMB (@lem3357150 _87274 s u x) (@lem3357156 _87274 s u x)). Qed.
Lemma lem3357158 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term120 _87274 s u x) = (term136 _87274 s u x).
Proof. exact (EQ_MP (@lem3357157 _87274 s u x) (@lem3357142 _87274 s u x)). Qed.
Lemma lem3357159 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term98 _87274 s u x) = (term136 _87274 s u x).
Proof. exact (TRANS (@lem3357138 _87274 s u x) (@lem3357158 _87274 s u x)). Qed.
Lemma lem3357160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357161 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term100 _87274 s u x) = (term137 _87274 s u x).
Proof. exact (MK_COMB (@lem3357160) (@lem3357159 _87274 s u x)). Qed.
Lemma lem3357163 {A : Type'} (P : A -> Prop) (Q : Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3357164 {_87274 : Type'} (P : type686 _87274) (Q : Prop) : (term140 _87274 P Q) = (term141 _87274 P Q).
Proof. exact (@lem3357163 (_87274 -> Prop) P Q). Qed.
Lemma lem3357165 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term142 _87274 s u x) = (term143 _87274 s u x).
Proof. exact (@lem3357164 _87274 (term70 _87274 s u x) (term90 _87274 s u x)). Qed.
Lemma lem3357166 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term144 _87274 s u x t) = (term58 _87274 s u t x).
Proof. exact (eq_refl (term144 _87274 s u x t)). Qed.
Lemma lem3357167 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term145 _87274 s u x) = (term70 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357166 _87274 s u t x)). Qed.
Lemma lem3357168 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357169 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term146 _87274 s u x) = (term71 _87274 s u x).
Proof. exact (MK_COMB (@lem3357168 _87274) (@lem3357167 _87274 s u x)). Qed.
Lemma lem3357170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357171 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term147 _87274 s u x) = (term92 _87274 s u x).
Proof. exact (MK_COMB (@lem3357170) (@lem3357169 _87274 s u x)). Qed.
Lemma lem3357172 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term90 _87274 s u x) = (term90 _87274 s u x).
Proof. exact (eq_refl (term90 _87274 s u x)). Qed.
Lemma lem3357173 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term142 _87274 s u x) = (term94 _87274 s u x).
Proof. exact (MK_COMB (@lem3357171 _87274 s u x) (@lem3357172 _87274 s u x)). Qed.
Lemma lem3357174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357175 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term148 _87274 s u x) = (term149 _87274 s u x).
Proof. exact (MK_COMB (@lem3357174) (@lem3357173 _87274 s u x)). Qed.
Lemma lem3357176 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term144 _87274 s u x t) = (term58 _87274 s u t x).
Proof. exact (eq_refl (term144 _87274 s u x t)). Qed.
Lemma lem3357177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357178 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term150 _87274 s u x t) = (term151 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357177) (@lem3357176 _87274 s u t x)). Qed.
Lemma lem3357179 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term90 _87274 s u x) = (term90 _87274 s u x).
Proof. exact (eq_refl (term90 _87274 s u x)). Qed.
Lemma lem3357180 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term152 _87274 t s u x) = (term153 _87274 t s u x).
Proof. exact (MK_COMB (@lem3357178 _87274 s u t x) (@lem3357179 _87274 s u x)). Qed.
Lemma lem3357181 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term154 _87274 s u x) = (term155 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357180 _87274 t s u x)). Qed.
Lemma lem3357182 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357183 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term143 _87274 s u x) = (term156 _87274 s u x).
Proof. exact (MK_COMB (@lem3357182 _87274) (@lem3357181 _87274 s u x)). Qed.
Lemma lem3357184 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term142 _87274 s u x) = (term143 _87274 s u x)) = ((term94 _87274 s u x) = (term156 _87274 s u x)).
Proof. exact (MK_COMB (@lem3357175 _87274 s u x) (@lem3357183 _87274 s u x)). Qed.
Lemma lem3357185 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term94 _87274 s u x) = (term156 _87274 s u x).
Proof. exact (EQ_MP (@lem3357184 _87274 s u x) (@lem3357165 _87274 s u x)). Qed.
Lemma lem3357186 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term102 _87274 s u x) = (term157 _87274 s u x).
Proof. exact (MK_COMB (@lem3357161 _87274 s u x) (@lem3357185 _87274 s u x)). Qed.
Lemma lem3357188 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3357189 {_87274 : Type'} (P : type686 _87274) (Q : type686 _87274) : (term160 _87274 P Q) = (term161 _87274 P Q).
Proof. exact (@lem3357188 (_87274 -> Prop) P Q). Qed.
Lemma lem3357190 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term162 _87274 s u x) = (term163 _87274 s u x).
Proof. exact (@lem3357189 _87274 (term135 _87274 s u x) (term155 _87274 s u x)). Qed.
Lemma lem3357191 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term164 _87274 s u x t) = (term133 _87274 s u t x).
Proof. exact (eq_refl (term164 _87274 s u x t)). Qed.
Lemma lem3357192 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term165 _87274 s u x) = (term135 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357191 _87274 s u t x)). Qed.
Lemma lem3357193 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357194 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term166 _87274 s u x) = (term136 _87274 s u x).
Proof. exact (MK_COMB (@lem3357193 _87274) (@lem3357192 _87274 s u x)). Qed.
Lemma lem3357195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357196 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term167 _87274 s u x) = (term137 _87274 s u x).
Proof. exact (MK_COMB (@lem3357195) (@lem3357194 _87274 s u x)). Qed.
Lemma lem3357197 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term168 _87274 s u x t) = (term153 _87274 t s u x).
Proof. exact (eq_refl (term168 _87274 s u x t)). Qed.
Lemma lem3357198 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term169 _87274 s u x) = (term155 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357197 _87274 t s u x)). Qed.
Lemma lem3357199 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357200 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term170 _87274 s u x) = (term156 _87274 s u x).
Proof. exact (MK_COMB (@lem3357199 _87274) (@lem3357198 _87274 s u x)). Qed.
Lemma lem3357201 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term162 _87274 s u x) = (term157 _87274 s u x).
Proof. exact (MK_COMB (@lem3357196 _87274 s u x) (@lem3357200 _87274 s u x)). Qed.
Lemma lem3357202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357203 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term171 _87274 s u x) = (term172 _87274 s u x).
Proof. exact (MK_COMB (@lem3357202) (@lem3357201 _87274 s u x)). Qed.
Lemma lem3357204 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term164 _87274 s u x t) = (term133 _87274 s u t x).
Proof. exact (eq_refl (term164 _87274 s u x t)). Qed.
Lemma lem3357205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357206 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term173 _87274 s u x t) = (term174 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357205) (@lem3357204 _87274 s u t x)). Qed.
Lemma lem3357207 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term168 _87274 s u x t) = (term153 _87274 t s u x).
Proof. exact (eq_refl (term168 _87274 s u x t)). Qed.
Lemma lem3357208 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term175 _87274 s u x t) = (term176 _87274 t s u x).
Proof. exact (MK_COMB (@lem3357206 _87274 s u t x) (@lem3357207 _87274 t s u x)). Qed.
Lemma lem3357209 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term177 _87274 s u x) = (term178 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357208 _87274 t s u x)). Qed.
Lemma lem3357210 {_87274 : Type'} : (@ex (_87274 -> Prop)) = (@ex (_87274 -> Prop)).
Proof. exact (eq_refl (@ex (_87274 -> Prop))). Qed.
Lemma lem3357211 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term163 _87274 s u x) = (term179 _87274 s u x).
Proof. exact (MK_COMB (@lem3357210 _87274) (@lem3357209 _87274 s u x)). Qed.
Lemma lem3357212 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : ((term162 _87274 s u x) = (term163 _87274 s u x)) = ((term157 _87274 s u x) = (term179 _87274 s u x)).
Proof. exact (MK_COMB (@lem3357203 _87274 s u x) (@lem3357211 _87274 s u x)). Qed.
Lemma lem3357213 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term157 _87274 s u x) = (term179 _87274 s u x).
Proof. exact (EQ_MP (@lem3357212 _87274 s u x) (@lem3357190 _87274 s u x)). Qed.
Lemma lem3357215 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term102 _87274 s u x) = (term179 _87274 s u x).
Proof. exact (TRANS (@lem3357186 _87274 s u x) (@lem3357213 _87274 s u x)). Qed.
Lemma lem3357216 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term54 _87274 s u x) = (term179 _87274 s u x).
Proof. exact (TRANS (@lem3356943 _87274 s u x) (@lem3357215 _87274 s u x)). Qed.
Lemma lem3357217 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term54 _87274 s u x) : term179 _87274 s u x.
Proof. exact (EQ_MP (@lem3357216 _87274 s u x) (@lem3356858 _87274 s u x h1)). Qed.
Lemma lem3357218 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term176 _87274 t s u x) : term176 _87274 t s u x.
Proof. exact (h1). Qed.
Lemma lem3357223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357224 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357223 _87274 Prop f x). Qed.
Lemma lem3357226 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357224 _87274 t x). Qed.
Lemma lem3357227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3357232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357233 {_87274 : Type'} (f : type686 _87274) (x : _87274 -> Prop) : (f x) = (@I ((_87274 -> Prop) -> Prop) f x).
Proof. exact (@lem3357232 (_87274 -> Prop) Prop f x). Qed.
Lemma lem3357235 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357233 _87274 u t). Qed.
Lemma lem3357236 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term180 _87274 u t) = (term181 _87274 u t).
Proof. exact (MK_COMB (@lem3357227) (@lem3357235 _87274 u t)). Qed.
Lemma lem3357237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357238 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term182 _87274 u t) = (term183 _87274 u t).
Proof. exact (MK_COMB (@lem3357237) (@lem3357236 _87274 u t)). Qed.
Lemma lem3357239 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term76 _87274 u t x) = (term184 _87274 u t x).
Proof. exact (MK_COMB (@lem3357238 _87274 u t) (@lem3357226 _87274 t x)). Qed.
Lemma lem3357240 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term84 _87274 u x) = (term185 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357239 _87274 u t x)). Qed.
Lemma lem3357241 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3357242 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term85 _87274 u x) = (term186 _87274 u x).
Proof. exact (MK_COMB (@lem3357241 _87274) (@lem3357240 _87274 u x)). Qed.
Lemma lem3357247 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357248 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357247 _87274 Prop f x). Qed.
Lemma lem3357250 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (s x) = (@I (_87274 -> Prop) s x).
Proof. exact (@lem3357248 _87274 s x). Qed.
Lemma lem3357251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357252 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term24 _87274 s x) = (term187 _87274 s x).
Proof. exact (MK_COMB (@lem3357251) (@lem3357250 _87274 s x)). Qed.
Lemma lem3357253 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term90 _87274 s u x) = (term188 _87274 s u x).
Proof. exact (MK_COMB (@lem3357252 _87274 s x) (@lem3357242 _87274 u x)). Qed.
Lemma lem3357254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3357259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357260 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357259 _87274 Prop f x). Qed.
Lemma lem3357262 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357260 _87274 t x). Qed.
Lemma lem3357263 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term109 _87274 t x) = (term189 _87274 t x).
Proof. exact (MK_COMB (@lem3357254) (@lem3357262 _87274 t x)). Qed.
Lemma lem3357268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357269 {_87274 : Type'} (f : type686 _87274) (x : _87274 -> Prop) : (f x) = (@I ((_87274 -> Prop) -> Prop) f x).
Proof. exact (@lem3357268 (_87274 -> Prop) Prop f x). Qed.
Lemma lem3357271 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357269 _87274 u t). Qed.
Lemma lem3357278 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) : (term8 _87274 t s) = (term8 _87274 t s).
Proof. exact (eq_refl (term8 _87274 t s)). Qed.
Lemma lem3357279 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term9 _87274 s u t) = (term190 _87274 s u t).
Proof. exact (MK_COMB (@lem3357278 _87274 t s) (@lem3357271 _87274 u t)). Qed.
Lemma lem3357280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357281 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term191 _87274 s u t) = (term192 _87274 s u t).
Proof. exact (MK_COMB (@lem3357280) (@lem3357279 _87274 s u t)). Qed.
Lemma lem3357282 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term58 _87274 s u t x) = (term193 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357281 _87274 s u t) (@lem3357263 _87274 t x)). Qed.
Lemma lem3357283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357284 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term151 _87274 s u t x) = (term194 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357283) (@lem3357282 _87274 s u t x)). Qed.
Lemma lem3357285 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term153 _87274 t s u x) = (term195 _87274 t s u x).
Proof. exact (MK_COMB (@lem3357284 _87274 s u t x) (@lem3357253 _87274 s u x)). Qed.
Lemma lem3357286 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3357291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357292 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357291 _87274 Prop f x). Qed.
Lemma lem3357294 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357292 _87274 t x). Qed.
Lemma lem3357295 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term109 _87274 t x) = (term189 _87274 t x).
Proof. exact (MK_COMB (@lem3357286) (@lem3357294 _87274 t x)). Qed.
Lemma lem3357300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357301 {_87274 : Type'} (f : type686 _87274) (x : _87274 -> Prop) : (f x) = (@I ((_87274 -> Prop) -> Prop) f x).
Proof. exact (@lem3357300 (_87274 -> Prop) Prop f x). Qed.
Lemma lem3357303 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357301 _87274 u t). Qed.
Lemma lem3357304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357305 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term196 _87274 u t) = (term197 _87274 u t).
Proof. exact (MK_COMB (@lem3357304) (@lem3357303 _87274 u t)). Qed.
Lemma lem3357306 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term75 _87274 u t x) = (term198 _87274 u t x).
Proof. exact (MK_COMB (@lem3357305 _87274 u t) (@lem3357295 _87274 t x)). Qed.
Lemma lem3357307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3357312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357313 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357312 _87274 Prop f x). Qed.
Lemma lem3357315 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (s x) = (@I (_87274 -> Prop) s x).
Proof. exact (@lem3357313 _87274 s x). Qed.
Lemma lem3357316 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term109 _87274 s x) = (term189 _87274 s x).
Proof. exact (MK_COMB (@lem3357307) (@lem3357315 _87274 s x)). Qed.
Lemma lem3357317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357318 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term86 _87274 s x) = (term199 _87274 s x).
Proof. exact (MK_COMB (@lem3357317) (@lem3357316 _87274 s x)). Qed.
Lemma lem3357319 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term116 _87274 s u t x) = (term200 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357318 _87274 s x) (@lem3357306 _87274 u t x)). Qed.
Lemma lem3357324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357325 {_87274 : Type'} (f : _87274 -> Prop) (x : _87274) : (f x) = (@I (_87274 -> Prop) f x).
Proof. exact (@lem3357324 _87274 Prop f x). Qed.
Lemma lem3357327 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357325 _87274 t x). Qed.
Lemma lem3357328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3357333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3357334 {_87274 : Type'} (f : type686 _87274) (x : _87274 -> Prop) : (f x) = (@I ((_87274 -> Prop) -> Prop) f x).
Proof. exact (@lem3357333 (_87274 -> Prop) Prop f x). Qed.
Lemma lem3357336 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357334 _87274 u t). Qed.
Lemma lem3357337 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term180 _87274 u t) = (term181 _87274 u t).
Proof. exact (MK_COMB (@lem3357328) (@lem3357336 _87274 u t)). Qed.
Lemma lem3357346 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) : (term201 _87274 t s) = (term201 _87274 t s).
Proof. exact (eq_refl (term201 _87274 t s)). Qed.
Lemma lem3357347 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term56 _87274 s u t) = (term202 _87274 s u t).
Proof. exact (MK_COMB (@lem3357346 _87274 t s) (@lem3357337 _87274 u t)). Qed.
Lemma lem3357348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357349 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) : (term60 _87274 s u t) = (term203 _87274 s u t).
Proof. exact (MK_COMB (@lem3357348) (@lem3357347 _87274 s u t)). Qed.
Lemma lem3357350 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term62 _87274 s u t x) = (term204 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357349 _87274 s u t) (@lem3357327 _87274 t x)). Qed.
Lemma lem3357351 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term72 _87274 s u x) = (term205 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357350 _87274 s u t x)). Qed.
Lemma lem3357352 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3357353 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term73 _87274 s u x) = (term206 _87274 s u x).
Proof. exact (MK_COMB (@lem3357352 _87274) (@lem3357351 _87274 s u x)). Qed.
Lemma lem3357354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3357355 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term96 _87274 s u x) = (term207 _87274 s u x).
Proof. exact (MK_COMB (@lem3357354) (@lem3357353 _87274 s u x)). Qed.
Lemma lem3357356 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term133 _87274 s u t x) = (term208 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357355 _87274 s u x) (@lem3357319 _87274 s u t x)). Qed.
Lemma lem3357357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3357358 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term174 _87274 s u t x) = (term209 _87274 s u t x).
Proof. exact (MK_COMB (@lem3357357) (@lem3357356 _87274 s u t x)). Qed.
Lemma lem3357359 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term176 _87274 t s u x) = (term210 _87274 t s u x).
Proof. exact (MK_COMB (@lem3357358 _87274 s u t x) (@lem3357285 _87274 t s u x)). Qed.
Lemma lem3357360 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term176 _87274 t s u x) : term210 _87274 t s u x.
Proof. exact (EQ_MP (@lem3357359 _87274 t s u x) (@lem3357218 _87274 t s u x h1)). Qed.
Lemma lem3357361 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term208 _87274 s u t x.
Proof. exact (h1). Qed.
Lemma lem3357362 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term195 _87274 t s u x.
Proof. exact (h1). Qed.
Lemma lem3357363 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term200 _87274 s u t x.
Proof. exact (proj2 (@lem3357361 _87274 s u t x h1)). Qed.
Lemma lem3357364 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term206 _87274 s u x.
Proof. exact (proj1 (@lem3357361 _87274 s u t x h1)). Qed.
Lemma lem3357366 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : term198 _87274 u t x.
Proof. exact (h1). Qed.
Lemma lem3357369 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term188 _87274 s u x.
Proof. exact (proj2 (@lem3357362 _87274 t s u x h1)). Qed.
Lemma lem3357370 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term193 _87274 s u t x.
Proof. exact (proj1 (@lem3357362 _87274 t s u x h1)). Qed.
Lemma lem3357371 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term186 _87274 u x.
Proof. exact (proj2 (@lem3357369 _87274 t s u x h1)). Qed.
Lemma lem3357374 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term190 _87274 s u t.
Proof. exact (proj1 (@lem3357370 _87274 t s u x h1)). Qed.
Lemma lem3357394 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term204 _87274 s u t x) = (term211 _87274 s u t x).
Proof. exact (@lem19699 (term212 _87274 t s) (term181 _87274 u t) (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357395 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term205 _87274 s u x) = (term213 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357394 _87274 s u t x)). Qed.
Lemma lem3357396 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3357398 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term206 _87274 s u x) = (term214 _87274 s u x).
Proof. exact (MK_COMB (@lem3357396 _87274) (@lem3357395 _87274 s u x)). Qed.
Lemma lem3357399 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term214 _87274 s u x.
Proof. exact (EQ_MP (@lem3357398 _87274 s u x) (@lem3357364 _87274 s u t x h1)). Qed.
Lemma lem3357403 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) : term189 _87274 s x.
Proof. exact (h1). Qed.
Lemma lem3357421 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term204 _87274 s u t x) = (term211 _87274 s u t x).
Proof. exact (@lem19699 (term212 _87274 t s) (term181 _87274 u t) (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357422 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term205 _87274 s u x) = (term213 _87274 s u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357421 _87274 s u t x)). Qed.
Lemma lem3357423 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3357425 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term206 _87274 s u x) = (term214 _87274 s u x).
Proof. exact (MK_COMB (@lem3357423 _87274) (@lem3357422 _87274 s u x)). Qed.
Lemma lem3357426 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term214 _87274 s u x.
Proof. exact (EQ_MP (@lem3357425 _87274 s u x) (@lem3357364 _87274 s u t x h1)). Qed.
Lemma lem3357459 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : t = s) : t = s.
Proof. exact (h1). Qed.
Lemma lem3357471 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) : (term184 _87274 u t x) = (term184 _87274 u t x).
Proof. exact (eq_refl (term184 _87274 u t x)). Qed.
Lemma lem3357472 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term185 _87274 u x) = (term185 _87274 u x).
Proof. exact (fun_ext (fun t : _87274 -> Prop => @lem3357471 _87274 u t x)). Qed.
Lemma lem3357473 {_87274 : Type'} : (@all (_87274 -> Prop)) = (@all (_87274 -> Prop)).
Proof. exact (eq_refl (@all (_87274 -> Prop))). Qed.
Lemma lem3357475 {_87274 : Type'} (u : type686 _87274) (x : _87274) : (term186 _87274 u x) = (term186 _87274 u x).
Proof. exact (MK_COMB (@lem3357473 _87274) (@lem3357472 _87274 u x)). Qed.
Lemma lem3357476 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term186 _87274 u x.
Proof. exact (EQ_MP (@lem3357475 _87274 u x) (@lem3357371 _87274 t s u x h1)). Qed.
Lemma lem3357484 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (h1 : @I ((_87274 -> Prop) -> Prop) u t) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3357485 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term215 _87274 s u x _35033.
Proof. exact (@lem3357399 _87274 s u t x h1 _35033). Qed.
Lemma lem3357486 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (_35033 : _87274 -> Prop) (x : _87274) : (term215 _87274 s u x _35033) = (term211 _87274 s u _35033 x).
Proof. exact (eq_refl (term215 _87274 s u x _35033)). Qed.
Lemma lem3357487 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term211 _87274 s u _35033 x.
Proof. exact (EQ_MP (@lem3357486 _87274 s u _35033 x) (@lem3357485 _87274 _35033 s u t x h1)). Qed.
Lemma lem3357488 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term215 _87274 s u x _35034.
Proof. exact (@lem3357426 _87274 s u t x h1 _35034). Qed.
Lemma lem3357489 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (_35034 : _87274 -> Prop) (x : _87274) : (term215 _87274 s u x _35034) = (term211 _87274 s u _35034 x).
Proof. exact (eq_refl (term215 _87274 s u x _35034)). Qed.
Lemma lem3357490 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term211 _87274 s u _35034 x.
Proof. exact (EQ_MP (@lem3357489 _87274 s u _35034 x) (@lem3357488 _87274 _35034 s u t x h1)). Qed.
Lemma lem3357494 {_87274 : Type'} (_35036 : _87274 -> Prop) (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term216 _87274 u x _35036.
Proof. exact (@lem3357476 _87274 t s u x h1 _35036). Qed.
Lemma lem3357495 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) (x : _87274) : (term216 _87274 u x _35036) = (term184 _87274 u _35036 x).
Proof. exact (eq_refl (term216 _87274 u x _35036)). Qed.
Lemma lem3357502 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) : term189 _87274 s x.
Proof. exact (h1). Qed.
Lemma lem3357508 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term217 _87274 s _35033 x.
Proof. exact (proj1 (@lem3357487 _87274 _35033 s u t x h1)). Qed.
Lemma lem3357518 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : term189 _87274 t x.
Proof. exact (proj2 (@lem3357366 _87274 u t x h1)). Qed.
Lemma lem3357530 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term184 _87274 u _35034 x.
Proof. exact (proj2 (@lem3357490 _87274 _35034 s u t x h1)). Qed.
Lemma lem3357540 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term189 _87274 t x.
Proof. exact (proj2 (@lem3357370 _87274 t s u x h1)). Qed.
Lemma lem3357542 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : t = s) : t = s.
Proof. exact (h1). Qed.
Lemma lem3357550 {_87274 : Type'} (_35036 : _87274 -> Prop) (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term184 _87274 u _35036 x.
Proof. exact (EQ_MP (@lem3357495 _87274 u _35036 x) (@lem3357494 _87274 _35036 t s u x h1)). Qed.
Lemma lem3357552 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term189 _87274 t x.
Proof. exact (proj2 (@lem3357370 _87274 t s u x h1)). Qed.
Lemma lem3357554 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (h1 : @I ((_87274 -> Prop) -> Prop) u t) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3357597 {_87274 : Type'} (x : _87274) : (term218 _87274 x) = (term218 _87274 x).
Proof. exact (eq_refl (term218 _87274 x)). Qed.
Lemma lem3357598 {_87274 : Type'} (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : t = s) : (term219 _87274 x t) = (term219 _87274 x s).
Proof. exact (MK_COMB (@lem3357597 _87274 x) (@lem3357542 _87274 t s h1)). Qed.
Lemma lem3357599 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term219 _87274 x s) = (term189 _87274 s x).
Proof. exact (eq_refl (term219 _87274 x s)). Qed.
Lemma lem3357600 {_87274 : Type'} (x : _87274) (t : _87274 -> Prop) : (term220 _87274 x t) = (term220 _87274 x t).
Proof. exact (eq_refl (term220 _87274 x t)). Qed.
Lemma lem3357601 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (x : _87274) : ((term219 _87274 x t) = (term219 _87274 x s)) = ((term219 _87274 x t) = (term189 _87274 s x)).
Proof. exact (MK_COMB (@lem3357600 _87274 x t) (@lem3357599 _87274 s x)). Qed.
Lemma lem3357602 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term219 _87274 x t) = (term189 _87274 t x).
Proof. exact (eq_refl (term219 _87274 x t)). Qed.
Lemma lem3357603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357604 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term220 _87274 x t) = (term221 _87274 t x).
Proof. exact (MK_COMB (@lem3357603) (@lem3357602 _87274 t x)). Qed.
Lemma lem3357605 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term189 _87274 s x) = (term189 _87274 s x).
Proof. exact (eq_refl (term189 _87274 s x)). Qed.
Lemma lem3357606 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (x : _87274) : ((term219 _87274 x t) = (term189 _87274 s x)) = ((term189 _87274 t x) = (term189 _87274 s x)).
Proof. exact (MK_COMB (@lem3357604 _87274 t x) (@lem3357605 _87274 s x)). Qed.
Lemma lem3357607 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (x : _87274) : ((term219 _87274 x t) = (term219 _87274 x s)) = ((term189 _87274 t x) = (term189 _87274 s x)).
Proof. exact (TRANS (@lem3357601 _87274 t s x) (@lem3357606 _87274 t s x)). Qed.
Lemma lem3357608 {_87274 : Type'} (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : t = s) : (term189 _87274 t x) = (term189 _87274 s x).
Proof. exact (EQ_MP (@lem3357607 _87274 t s x) (@lem3357598 _87274 x t s h1)). Qed.
Lemma lem3357609 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : term189 _87274 s x.
Proof. exact (EQ_MP (@lem3357608 _87274 x t s h2) (@lem3357540 _87274 t s u x h1)). Qed.
Lemma lem3357655 {_87274 : Type'} (x : _87274 -> Prop) : x = x.
Proof. exact (@lem21386 (_87274 -> Prop) x). Qed.
Lemma lem3357656 {_87274 : Type'} (x : _87274 -> Prop) : x = x.
Proof. exact (@lem3357655 _87274 x). Qed.
Lemma lem3357657 {_87274 : Type'} (s : _87274 -> Prop) : s = s.
Proof. exact (@lem3357656 _87274 s). Qed.
Lemma lem3357658 {_87274 : Type'} (s : _87274 -> Prop) : term222 _87274 s.
Proof. exact (fun h0 : term223 _87274 s => @lem3357657 _87274 s). Qed.
Lemma lem3357660 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357661 {_87274 : Type'} (s : _87274 -> Prop) : (term222 _87274 s) = (s = s).
Proof. exact (@lem3357660 (s = s)). Qed.
Lemma lem3357662 {_87274 : Type'} (s : _87274 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3357661 _87274 s) (@lem3357658 _87274 s)). Qed.
Lemma lem3357668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3357669 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term217 _87274 s _35033 x) = (term225 _87274 x _35033 s).
Proof. exact (@lem3357668 (@I (_87274 -> Prop) _35033 x) (term212 _87274 _35033 s)). Qed.
Lemma lem3357677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357678 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term226 _87274 s _35033 x) = (term227 _87274 x _35033 s).
Proof. exact (MK_COMB (@lem3357677) (@lem3357669 _87274 x _35033 s)). Qed.
Lemma lem3357686 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term225 _87274 x _35033 s) = (term225 _87274 x _35033 s).
Proof. exact (eq_refl (term225 _87274 x _35033 s)). Qed.
Lemma lem3357687 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : ((term217 _87274 s _35033 x) = (term225 _87274 x _35033 s)) = ((term225 _87274 x _35033 s) = (term225 _87274 x _35033 s)).
Proof. exact (MK_COMB (@lem3357678 _87274 x _35033 s) (@lem3357686 _87274 x _35033 s)). Qed.
Lemma lem3357689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3357690 (x : Prop) : (x = x) = True.
Proof. exact (@lem3357689 Prop x). Qed.
Lemma lem3357691 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : ((term225 _87274 x _35033 s) = (term225 _87274 x _35033 s)) = True.
Proof. exact (@lem3357690 (term225 _87274 x _35033 s)). Qed.
Lemma lem3357692 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : ((term217 _87274 s _35033 x) = (term225 _87274 x _35033 s)) = True.
Proof. exact (TRANS (@lem3357687 _87274 x _35033 s) (@lem3357691 _87274 x _35033 s)). Qed.
Lemma lem3357693 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : True = ((term217 _87274 s _35033 x) = (term225 _87274 x _35033 s)).
Proof. exact (SYM (@lem3357692 _87274 x _35033 s)). Qed.
Lemma lem3357694 {_87274 : Type'} (x : _87274) (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term217 _87274 s _35033 x) = (term225 _87274 x _35033 s).
Proof. exact (EQ_MP (@lem3357693 _87274 x _35033 s) (@lem0)). Qed.
Lemma lem3357695 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term225 _87274 x _35033 s.
Proof. exact (EQ_MP (@lem3357694 _87274 x _35033 s) (@lem3357508 _87274 _35033 s u t x h1)). Qed.
Lemma lem3357697 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3357698 {_87274 : Type'} (s : _87274 -> Prop) (_35033 : _87274 -> Prop) (x : _87274) : (term225 _87274 x _35033 s) = (term229 _87274 s _35033 x).
Proof. exact (@lem3357697 (term212 _87274 _35033 s) (@I (_87274 -> Prop) _35033 x)). Qed.
Lemma lem3357700 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3357701 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term230 _87274 _35033 s) = (_35033 = s).
Proof. exact (@lem3357700 (_35033 = s)). Qed.
Lemma lem3357702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3357703 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) : (term231 _87274 _35033 s) = (term232 _87274 _35033 s).
Proof. exact (MK_COMB (@lem3357702) (@lem3357701 _87274 _35033 s)). Qed.
Lemma lem3357704 {_87274 : Type'} (_35033 : _87274 -> Prop) (x : _87274) : (@I (_87274 -> Prop) _35033 x) = (@I (_87274 -> Prop) _35033 x).
Proof. exact (eq_refl (@I (_87274 -> Prop) _35033 x)). Qed.
Lemma lem3357705 {_87274 : Type'} (s : _87274 -> Prop) (_35033 : _87274 -> Prop) (x : _87274) : (term229 _87274 s _35033 x) = (term233 _87274 s _35033 x).
Proof. exact (MK_COMB (@lem3357703 _87274 _35033 s) (@lem3357704 _87274 _35033 x)). Qed.
Lemma lem3357706 {_87274 : Type'} (s : _87274 -> Prop) (_35033 : _87274 -> Prop) (x : _87274) : (term225 _87274 x _35033 s) = (term233 _87274 s _35033 x).
Proof. exact (TRANS (@lem3357698 _87274 s _35033 x) (@lem3357705 _87274 s _35033 x)). Qed.
Lemma lem3357709 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term233 _87274 s _35033 x.
Proof. exact (EQ_MP (@lem3357706 _87274 s _35033 x) (@lem3357695 _87274 _35033 s u t x h1)). Qed.
Lemma lem3357710 {_87274 : Type'} (_35033 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term233 _87274 s _35033 x.
Proof. exact (@lem3357709 _87274 _35033 s u t x h1). Qed.
Lemma lem3357711 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term234 _87274 s x.
Proof. exact (@lem3357710 _87274 s s u t x h1). Qed.
Lemma lem3357714 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : @I (_87274 -> Prop) s x.
Proof. exact (@lem3357711 _87274 s u t x h1 (@lem3357662 _87274 s)). Qed.
Lemma lem3357715 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term235 _87274 s x.
Proof. exact (fun h0 : term189 _87274 s x => @lem3357714 _87274 s u t x h1). Qed.
Lemma lem3357717 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357718 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term235 _87274 s x) = (@I (_87274 -> Prop) s x).
Proof. exact (@lem3357717 (@I (_87274 -> Prop) s x)). Qed.
Lemma lem3357719 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : @I (_87274 -> Prop) s x.
Proof. exact (EQ_MP (@lem3357718 _87274 s x) (@lem3357715 _87274 s u t x h1)). Qed.
Lemma lem3357722 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3357724 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term189 _87274 s x) = (term236 _87274 s x).
Proof. exact (@lem3357722 (@I (_87274 -> Prop) s x)). Qed.
Lemma lem3357727 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) : term236 _87274 s x.
Proof. exact (EQ_MP (@lem3357724 _87274 s x) (@lem3357502 _87274 s x h1)). Qed.
Lemma lem3357730 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : False.
Proof. exact (@lem3357727 _87274 s x h1 (@lem3357719 _87274 s u t x h2)). Qed.
Lemma lem3357731 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : term237.
Proof. exact (fun h0 : ~ False => @lem3357730 _87274 s u t x h1 h2). Qed.
Lemma lem3357733 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357734 : term237 = False.
Proof. exact (@lem3357733 False). Qed.
Lemma lem3357735 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : False.
Proof. exact (EQ_MP (@lem3357734) (@lem3357731 _87274 s u t x h1 h2)). Qed.
Lemma lem3357781 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (proj1 (@lem3357366 _87274 u t x h1)). Qed.
Lemma lem3357782 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : term238 _87274 u t.
Proof. exact (fun h0 : term181 _87274 u t => @lem3357781 _87274 u t x h1). Qed.
Lemma lem3357784 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357785 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term238 _87274 u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357784 (@I ((_87274 -> Prop) -> Prop) u t)). Qed.
Lemma lem3357786 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem3357785 _87274 u t) (@lem3357782 _87274 u t x h1)). Qed.
Lemma lem3357792 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3357793 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : (term184 _87274 u _35034 x) = (term239 _87274 x u _35034).
Proof. exact (@lem3357792 (@I (_87274 -> Prop) _35034 x) (term181 _87274 u _35034)). Qed.
Lemma lem3357799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357800 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : (term240 _87274 u _35034 x) = (term241 _87274 x u _35034).
Proof. exact (MK_COMB (@lem3357799) (@lem3357793 _87274 x u _35034)). Qed.
Lemma lem3357806 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : (term239 _87274 x u _35034) = (term239 _87274 x u _35034).
Proof. exact (eq_refl (term239 _87274 x u _35034)). Qed.
Lemma lem3357807 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : ((term184 _87274 u _35034 x) = (term239 _87274 x u _35034)) = ((term239 _87274 x u _35034) = (term239 _87274 x u _35034)).
Proof. exact (MK_COMB (@lem3357800 _87274 x u _35034) (@lem3357806 _87274 x u _35034)). Qed.
Lemma lem3357809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3357810 (x : Prop) : (x = x) = True.
Proof. exact (@lem3357809 Prop x). Qed.
Lemma lem3357811 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : ((term239 _87274 x u _35034) = (term239 _87274 x u _35034)) = True.
Proof. exact (@lem3357810 (term239 _87274 x u _35034)). Qed.
Lemma lem3357812 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : ((term184 _87274 u _35034 x) = (term239 _87274 x u _35034)) = True.
Proof. exact (TRANS (@lem3357807 _87274 x u _35034) (@lem3357811 _87274 x u _35034)). Qed.
Lemma lem3357813 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : True = ((term184 _87274 u _35034 x) = (term239 _87274 x u _35034)).
Proof. exact (SYM (@lem3357812 _87274 x u _35034)). Qed.
Lemma lem3357814 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35034 : _87274 -> Prop) : (term184 _87274 u _35034 x) = (term239 _87274 x u _35034).
Proof. exact (EQ_MP (@lem3357813 _87274 x u _35034) (@lem0)). Qed.
Lemma lem3357815 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term239 _87274 x u _35034.
Proof. exact (EQ_MP (@lem3357814 _87274 x u _35034) (@lem3357530 _87274 _35034 s u t x h1)). Qed.
Lemma lem3357817 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3357818 {_87274 : Type'} (u : type686 _87274) (_35034 : _87274 -> Prop) (x : _87274) : (term239 _87274 x u _35034) = (term242 _87274 u _35034 x).
Proof. exact (@lem3357817 (term181 _87274 u _35034) (@I (_87274 -> Prop) _35034 x)). Qed.
Lemma lem3357820 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3357821 {_87274 : Type'} (u : type686 _87274) (_35034 : _87274 -> Prop) : (term243 _87274 u _35034) = (@I ((_87274 -> Prop) -> Prop) u _35034).
Proof. exact (@lem3357820 (@I ((_87274 -> Prop) -> Prop) u _35034)). Qed.
Lemma lem3357822 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3357823 {_87274 : Type'} (u : type686 _87274) (_35034 : _87274 -> Prop) : (term244 _87274 u _35034) = (term245 _87274 u _35034).
Proof. exact (MK_COMB (@lem3357822) (@lem3357821 _87274 u _35034)). Qed.
Lemma lem3357824 {_87274 : Type'} (_35034 : _87274 -> Prop) (x : _87274) : (@I (_87274 -> Prop) _35034 x) = (@I (_87274 -> Prop) _35034 x).
Proof. exact (eq_refl (@I (_87274 -> Prop) _35034 x)). Qed.
Lemma lem3357825 {_87274 : Type'} (u : type686 _87274) (_35034 : _87274 -> Prop) (x : _87274) : (term242 _87274 u _35034 x) = (term246 _87274 u _35034 x).
Proof. exact (MK_COMB (@lem3357823 _87274 u _35034) (@lem3357824 _87274 _35034 x)). Qed.
Lemma lem3357826 {_87274 : Type'} (u : type686 _87274) (_35034 : _87274 -> Prop) (x : _87274) : (term239 _87274 x u _35034) = (term246 _87274 u _35034 x).
Proof. exact (TRANS (@lem3357818 _87274 u _35034 x) (@lem3357825 _87274 u _35034 x)). Qed.
Lemma lem3357829 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term246 _87274 u _35034 x.
Proof. exact (EQ_MP (@lem3357826 _87274 u _35034 x) (@lem3357815 _87274 _35034 s u t x h1)). Qed.
Lemma lem3357830 {_87274 : Type'} (_35034 : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term246 _87274 u _35034 x.
Proof. exact (@lem3357829 _87274 _35034 s u t x h1). Qed.
Lemma lem3357831 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : term246 _87274 u t x.
Proof. exact (@lem3357830 _87274 t s u t x h1). Qed.
Lemma lem3357834 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : @I (_87274 -> Prop) t x.
Proof. exact (@lem3357831 _87274 s u t x h1 (@lem3357786 _87274 u t x h2)). Qed.
Lemma lem3357835 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : term235 _87274 t x.
Proof. exact (fun h0 : term189 _87274 t x => @lem3357834 _87274 s u t x h1 h2). Qed.
Lemma lem3357837 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357838 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term235 _87274 t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357837 (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357839 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : @I (_87274 -> Prop) t x.
Proof. exact (EQ_MP (@lem3357838 _87274 t x) (@lem3357835 _87274 s u t x h1 h2)). Qed.
Lemma lem3357842 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3357844 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term189 _87274 t x) = (term236 _87274 t x).
Proof. exact (@lem3357842 (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357847 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term198 _87274 u t x) : term236 _87274 t x.
Proof. exact (EQ_MP (@lem3357844 _87274 t x) (@lem3357518 _87274 u t x h1)). Qed.
Lemma lem3357850 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : False.
Proof. exact (@lem3357847 _87274 u t x h2 (@lem3357839 _87274 s u t x h1 h2)). Qed.
Lemma lem3357851 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : term237.
Proof. exact (fun h0 : ~ False => @lem3357850 _87274 s u t x h1 h2). Qed.
Lemma lem3357853 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357854 : term237 = False.
Proof. exact (@lem3357853 False). Qed.
Lemma lem3357855 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) (h2 : term198 _87274 u t x) : False.
Proof. exact (EQ_MP (@lem3357854) (@lem3357851 _87274 s u t x h1 h2)). Qed.
Lemma lem3357857 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : @I (_87274 -> Prop) s x.
Proof. exact (proj1 (@lem3357369 _87274 t s u x h1)). Qed.
Lemma lem3357858 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term235 _87274 s x.
Proof. exact (fun h0 : term189 _87274 s x => @lem3357857 _87274 t s u x h1). Qed.
Lemma lem3357860 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357861 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term235 _87274 s x) = (@I (_87274 -> Prop) s x).
Proof. exact (@lem3357860 (@I (_87274 -> Prop) s x)). Qed.
Lemma lem3357862 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : @I (_87274 -> Prop) s x.
Proof. exact (EQ_MP (@lem3357861 _87274 s x) (@lem3357858 _87274 t s u x h1)). Qed.
Lemma lem3357865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3357867 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) : (term189 _87274 s x) = (term236 _87274 s x).
Proof. exact (@lem3357865 (@I (_87274 -> Prop) s x)). Qed.
Lemma lem3357870 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : term236 _87274 s x.
Proof. exact (EQ_MP (@lem3357867 _87274 s x) (@lem3357609 _87274 u x t s h1 h2)). Qed.
Lemma lem3357873 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : False.
Proof. exact (@lem3357870 _87274 u x t s h1 h2 (@lem3357862 _87274 t s u x h1)). Qed.
Lemma lem3357874 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : term237.
Proof. exact (fun h0 : ~ False => @lem3357873 _87274 u x t s h1 h2). Qed.
Lemma lem3357876 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357877 : term237 = False.
Proof. exact (@lem3357876 False). Qed.
Lemma lem3357880 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (h1 : @I ((_87274 -> Prop) -> Prop) u t) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3357881 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (h1 : @I ((_87274 -> Prop) -> Prop) u t) : term238 _87274 u t.
Proof. exact (fun h0 : term181 _87274 u t => @lem3357880 _87274 u t h1). Qed.
Lemma lem3357883 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357884 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) : (term238 _87274 u t) = (@I ((_87274 -> Prop) -> Prop) u t).
Proof. exact (@lem3357883 (@I ((_87274 -> Prop) -> Prop) u t)). Qed.
Lemma lem3357885 {_87274 : Type'} (u : type686 _87274) (t : _87274 -> Prop) (h1 : @I ((_87274 -> Prop) -> Prop) u t) : @I ((_87274 -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem3357884 _87274 u t) (@lem3357881 _87274 u t h1)). Qed.
Lemma lem3357891 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3357892 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : (term184 _87274 u _35036 x) = (term239 _87274 x u _35036).
Proof. exact (@lem3357891 (@I (_87274 -> Prop) _35036 x) (term181 _87274 u _35036)). Qed.
Lemma lem3357898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3357899 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : (term240 _87274 u _35036 x) = (term241 _87274 x u _35036).
Proof. exact (MK_COMB (@lem3357898) (@lem3357892 _87274 x u _35036)). Qed.
Lemma lem3357905 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : (term239 _87274 x u _35036) = (term239 _87274 x u _35036).
Proof. exact (eq_refl (term239 _87274 x u _35036)). Qed.
Lemma lem3357906 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : ((term184 _87274 u _35036 x) = (term239 _87274 x u _35036)) = ((term239 _87274 x u _35036) = (term239 _87274 x u _35036)).
Proof. exact (MK_COMB (@lem3357899 _87274 x u _35036) (@lem3357905 _87274 x u _35036)). Qed.
Lemma lem3357908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3357909 (x : Prop) : (x = x) = True.
Proof. exact (@lem3357908 Prop x). Qed.
Lemma lem3357910 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : ((term239 _87274 x u _35036) = (term239 _87274 x u _35036)) = True.
Proof. exact (@lem3357909 (term239 _87274 x u _35036)). Qed.
Lemma lem3357911 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : ((term184 _87274 u _35036 x) = (term239 _87274 x u _35036)) = True.
Proof. exact (TRANS (@lem3357906 _87274 x u _35036) (@lem3357910 _87274 x u _35036)). Qed.
Lemma lem3357912 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : True = ((term184 _87274 u _35036 x) = (term239 _87274 x u _35036)).
Proof. exact (SYM (@lem3357911 _87274 x u _35036)). Qed.
Lemma lem3357913 {_87274 : Type'} (x : _87274) (u : type686 _87274) (_35036 : _87274 -> Prop) : (term184 _87274 u _35036 x) = (term239 _87274 x u _35036).
Proof. exact (EQ_MP (@lem3357912 _87274 x u _35036) (@lem0)). Qed.
Lemma lem3357914 {_87274 : Type'} (_35036 : _87274 -> Prop) (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term239 _87274 x u _35036.
Proof. exact (EQ_MP (@lem3357913 _87274 x u _35036) (@lem3357550 _87274 _35036 t s u x h1)). Qed.
Lemma lem3357916 (b : Prop) (a : Prop) : (a \/ b) = (term228 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3357917 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) (x : _87274) : (term239 _87274 x u _35036) = (term242 _87274 u _35036 x).
Proof. exact (@lem3357916 (term181 _87274 u _35036) (@I (_87274 -> Prop) _35036 x)). Qed.
Lemma lem3357919 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3357920 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) : (term243 _87274 u _35036) = (@I ((_87274 -> Prop) -> Prop) u _35036).
Proof. exact (@lem3357919 (@I ((_87274 -> Prop) -> Prop) u _35036)). Qed.
Lemma lem3357921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3357922 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) : (term244 _87274 u _35036) = (term245 _87274 u _35036).
Proof. exact (MK_COMB (@lem3357921) (@lem3357920 _87274 u _35036)). Qed.
Lemma lem3357923 {_87274 : Type'} (_35036 : _87274 -> Prop) (x : _87274) : (@I (_87274 -> Prop) _35036 x) = (@I (_87274 -> Prop) _35036 x).
Proof. exact (eq_refl (@I (_87274 -> Prop) _35036 x)). Qed.
Lemma lem3357924 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) (x : _87274) : (term242 _87274 u _35036 x) = (term246 _87274 u _35036 x).
Proof. exact (MK_COMB (@lem3357922 _87274 u _35036) (@lem3357923 _87274 _35036 x)). Qed.
Lemma lem3357925 {_87274 : Type'} (u : type686 _87274) (_35036 : _87274 -> Prop) (x : _87274) : (term239 _87274 x u _35036) = (term246 _87274 u _35036 x).
Proof. exact (TRANS (@lem3357917 _87274 u _35036 x) (@lem3357924 _87274 u _35036 x)). Qed.
Lemma lem3357928 {_87274 : Type'} (_35036 : _87274 -> Prop) (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term246 _87274 u _35036 x.
Proof. exact (EQ_MP (@lem3357925 _87274 u _35036 x) (@lem3357914 _87274 _35036 t s u x h1)). Qed.
Lemma lem3357929 {_87274 : Type'} (_35036 : _87274 -> Prop) (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term246 _87274 u _35036 x.
Proof. exact (@lem3357928 _87274 _35036 t s u x h1). Qed.
Lemma lem3357930 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term246 _87274 u t x.
Proof. exact (@lem3357929 _87274 t t s u x h1). Qed.
Lemma lem3357933 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : @I (_87274 -> Prop) t x.
Proof. exact (@lem3357930 _87274 t s u x h1 (@lem3357885 _87274 u t h2)). Qed.
Lemma lem3357934 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : term235 _87274 t x.
Proof. exact (fun h0 : term189 _87274 t x => @lem3357933 _87274 s x u t h1 h2). Qed.
Lemma lem3357936 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357937 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term235 _87274 t x) = (@I (_87274 -> Prop) t x).
Proof. exact (@lem3357936 (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357938 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : @I (_87274 -> Prop) t x.
Proof. exact (EQ_MP (@lem3357937 _87274 t x) (@lem3357934 _87274 s x u t h1 h2)). Qed.
Lemma lem3357941 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3357943 {_87274 : Type'} (t : _87274 -> Prop) (x : _87274) : (term189 _87274 t x) = (term236 _87274 t x).
Proof. exact (@lem3357941 (@I (_87274 -> Prop) t x)). Qed.
Lemma lem3357946 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : term236 _87274 t x.
Proof. exact (EQ_MP (@lem3357943 _87274 t x) (@lem3357552 _87274 t s u x h1)). Qed.
Lemma lem3357949 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : False.
Proof. exact (@lem3357946 _87274 t s u x h1 (@lem3357938 _87274 s x u t h1 h2)). Qed.
Lemma lem3357950 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : term237.
Proof. exact (fun h0 : ~ False => @lem3357949 _87274 s x u t h1 h2). Qed.
Lemma lem3357952 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3357953 : term237 = False.
Proof. exact (@lem3357952 False). Qed.
Lemma lem3357954 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3357953) (@lem3357950 _87274 s x u t h1 h2)). Qed.
Lemma lem3357955 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3357877) (@lem3357874 _87274 u x t s h1 h2)). Qed.
Lemma lem3357956 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : (@I ((_87274 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_87274 -> Prop) -> Prop) u t => @lem3357954 _87274 s x u t h1 h2) (fun h3 : False => @lem3357554 _87274 u t h2)). Qed.
Lemma lem3357957 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3357956 _87274 s x u t h1 h2) (@lem3357554 _87274 u t h2)). Qed.
Lemma lem3357958 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3357955 _87274 u x t s h1 h2) (fun h3 : False => @lem3357542 _87274 t s h2)). Qed.
Lemma lem3357959 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3357958 _87274 u x t s h1 h2) (@lem3357542 _87274 t s h2)). Qed.
Lemma lem3357960 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : (term189 _87274 s x) = False.
Proof. exact (prop_ext (fun h3 : term189 _87274 s x => @lem3357735 _87274 s u t x h1 h2) (fun h3 : False => @lem3357502 _87274 s x h1)). Qed.
Lemma lem3357961 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : False.
Proof. exact (EQ_MP (@lem3357960 _87274 s u t x h1 h2) (@lem3357502 _87274 s x h1)). Qed.
Lemma lem3357962 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : (@I ((_87274 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_87274 -> Prop) -> Prop) u t => @lem3357957 _87274 s x u t h1 h2) (fun h3 : False => @lem3357484 _87274 u t h2)). Qed.
Lemma lem3357963 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3357962 _87274 s x u t h1 h2) (@lem3357484 _87274 u t h2)). Qed.
Lemma lem3357964 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3357959 _87274 u x t s h1 h2) (fun h3 : False => @lem3357459 _87274 t s h2)). Qed.
Lemma lem3357965 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3357964 _87274 u x t s h1 h2) (@lem3357459 _87274 t s h2)). Qed.
Lemma lem3357966 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : (term189 _87274 s x) = False.
Proof. exact (prop_ext (fun h3 : term189 _87274 s x => @lem3357961 _87274 s u t x h1 h2) (fun h3 : False => @lem3357403 _87274 s x h1)). Qed.
Lemma lem3357967 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : False.
Proof. exact (EQ_MP (@lem3357966 _87274 s u t x h1 h2) (@lem3357403 _87274 s x h1)). Qed.
Lemma lem3357968 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : (@I ((_87274 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_87274 -> Prop) -> Prop) u t => @lem3357963 _87274 s x u t h1 h2) (fun h3 : False => @lem3357484 _87274 u t h2)). Qed.
Lemma lem3357969 {_87274 : Type'} (s : _87274 -> Prop) (x : _87274) (u : type686 _87274) (t : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : @I ((_87274 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3357968 _87274 s x u t h1 h2) (@lem3357484 _87274 u t h2)). Qed.
Lemma lem3357970 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3357965 _87274 u x t s h1 h2) (fun h3 : False => @lem3357459 _87274 t s h2)). Qed.
Lemma lem3357971 {_87274 : Type'} (u : type686 _87274) (x : _87274) (t : _87274 -> Prop) (s : _87274 -> Prop) (h1 : term195 _87274 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3357970 _87274 u x t s h1 h2) (@lem3357459 _87274 t s h2)). Qed.
Lemma lem3357972 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : (term189 _87274 s x) = False.
Proof. exact (prop_ext (fun h3 : term189 _87274 s x => @lem3357967 _87274 s u t x h1 h2) (fun h3 : False => @lem3357403 _87274 s x h1)). Qed.
Lemma lem3357973 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term189 _87274 s x) (h2 : term208 _87274 s u t x) : False.
Proof. exact (EQ_MP (@lem3357972 _87274 s u t x h1 h2) (@lem3357403 _87274 s x h1)). Qed.
Lemma lem3357974 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term195 _87274 t s u x) : False.
Proof. exact (or_elim (@lem3357374 _87274 t s u x h1) (fun h0 : t = s => @lem3357971 _87274 u x t s h1 h0) (fun h0 : @I ((_87274 -> Prop) -> Prop) u t => @lem3357969 _87274 s x u t h1 h0)). Qed.
Lemma lem3357975 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (t : _87274 -> Prop) (x : _87274) (h1 : term208 _87274 s u t x) : False.
Proof. exact (or_elim (@lem3357363 _87274 s u t x h1) (fun h0 : term189 _87274 s x => @lem3357973 _87274 s u t x h0 h1) (fun h0 : term198 _87274 u t x => @lem3357855 _87274 s u t x h1 h0)). Qed.
Lemma lem3357976 {_87274 : Type'} (t : _87274 -> Prop) (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term176 _87274 t s u x) : False.
Proof. exact (or_elim (@lem3357360 _87274 t s u x h1) (fun h0 : term208 _87274 s u t x => @lem3357975 _87274 s u t x h0) (fun h0 : term195 _87274 t s u x => @lem3357974 _87274 t s u x h0)). Qed.
Lemma lem3357977 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term54 _87274 s u x) : False.
Proof. exact (ex_elim (@lem3357217 _87274 s u x h1) (fun t : _87274 -> Prop => fun h0 : term178 _87274 s u x t => @lem3357976 _87274 t s u x h0)). Qed.
Lemma lem3357978 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term54 _87274 s u x) : (term54 _87274 s u x) = False.
Proof. exact (prop_ext (fun h2 : term54 _87274 s u x => @lem3357977 _87274 s u x h1) (fun h2 : False => @lem3356858 _87274 s u x h1)). Qed.
Lemma lem3357979 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) (h1 : term54 _87274 s u x) : False.
Proof. exact (EQ_MP (@lem3357978 _87274 s u x h1) (@lem3356858 _87274 s u x h1)). Qed.
Lemma lem3357980 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : term53 _87274 s u x.
Proof. exact (fun h0 : term54 _87274 s u x => @lem3357979 _87274 s u x h0). Qed.
Lemma lem3357981 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (x : _87274) : (term16 _87274 s u x) = (term32 _87274 s u x).
Proof. exact (EQ_MP (@lem3356857 _87274 s u x) (@lem3357980 _87274 s u x)). Qed.
Lemma lem3357986 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term36 _87274 s u.
Proof. exact (fun x : _87274 => @lem3357981 _87274 s u x). Qed.
Lemma lem3357991 {_87274 : Type'} (u : type686 _87274) : term48 _87274 u.
Proof. exact (fun s : _87274 -> Prop => @lem3357986 _87274 s u). Qed.
Lemma lem3357996 {_87274 : Type'} : term52 _87274.
Proof. exact (fun u : type686 _87274 => @lem3357991 _87274 u). Qed.
Lemma lem3357997 {_87274 : Type'} : term51 _87274.
Proof. exact (EQ_MP (@lem3356853 _87274) (@lem3357996 _87274)). Qed.
Lemma lem3357998 {_87274 : Type'} (u : type686 _87274) : term247 _87274 u.
Proof. exact (@lem3357997 _87274 u). Qed.
Lemma lem3357999 {_87274 : Type'} (u : type686 _87274) : (term247 _87274 u) = (term47 _87274 u).
Proof. exact (eq_refl (term247 _87274 u)). Qed.
Lemma lem3358000 {_87274 : Type'} (u : type686 _87274) : term47 _87274 u.
Proof. exact (EQ_MP (@lem3357999 _87274 u) (@lem3357998 _87274 u)). Qed.
Lemma lem3358001 {_87274 : Type'} (u : type686 _87274) (s : _87274 -> Prop) : term248 _87274 u s.
Proof. exact (@lem3358000 _87274 u s). Qed.
Lemma lem3358002 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : (term248 _87274 u s) = (term38 _87274 s u).
Proof. exact (eq_refl (term248 _87274 u s)). Qed.
Lemma lem3358003 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term38 _87274 s u.
Proof. exact (EQ_MP (@lem3358002 _87274 s u) (@lem3358001 _87274 u s)). Qed.
Lemma lem3358005 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term38 _87274 s u.
Proof. exact (@lem3356722 _87274 s u (@lem3358003 _87274 s u)). Qed.
Lemma lem3358006 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term39 _87274 s u) : False.
Proof. exact (@lem3358005 _87274 s u (@lem3356706 _87274 s u h1)). Qed.
Lemma lem3358007 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term39 _87274 s u) : (term39 _87274 s u) = False.
Proof. exact (prop_ext (fun h2 : term39 _87274 s u => @lem3358006 _87274 s u h1) (fun h2 : False => @lem3356706 _87274 s u h1)). Qed.
Lemma lem3358008 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) (h1 : term39 _87274 s u) : False.
Proof. exact (EQ_MP (@lem3358007 _87274 s u h1) (@lem3356706 _87274 s u h1)). Qed.
Lemma lem3358009 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term38 _87274 s u.
Proof. exact (fun h0 : term39 _87274 s u => @lem3358008 _87274 s u h0). Qed.
Lemma lem3358010 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term36 _87274 s u.
Proof. exact (EQ_MP (@lem3356705 _87274 s u) (@lem3358009 _87274 s u)). Qed.
Lemma lem3358011 {_87274 : Type'} (s : _87274 -> Prop) (u : type686 _87274) : term35 _87274 s u.
Proof. exact (EQ_MP (@lem3356701 _87274 s u) (@lem3358010 _87274 s u)). Qed.
