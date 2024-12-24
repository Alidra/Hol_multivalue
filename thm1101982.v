Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101982_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1101651 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1101652 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1101653 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1101652 A B f) (@lem1101651 A B f)). Qed.
Lemma lem1101654 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1101653 A B f y). Qed.
Lemma lem1101655 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1101658 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : ITLIST' = (term4 _25350 _25351 _17984).
Proof. exact (h1). Qed.
Lemma lem1101659 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101660 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101658 _25350 _25351 ITLIST' _17984 h1) (@lem1101659 _25350 _25351 f)). Qed.
Lemma lem1101662 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101663 {_25350 _25351 : Type'} (f : type725 _25350 _25351) (y : type1467 _25350 _25351) : (term6 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101662 (type1467 _25350 _25351) (type1152 _25350 _25351) f y). Qed.
Lemma lem1101664 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (@lem1101663 _25350 _25351 (term4 _25350 _25351 _17984) f). Qed.
Lemma lem1101665 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17981 : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 _17981) = (term8 _25350 _25351 _17984 _17981).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101666 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) : (term9 _25350 _25351 _17984) = (term4 _25350 _25351 _17984).
Proof. exact (fun_ext (fun _17981 : type1467 _25350 _25351 => @lem1101665 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101667 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101668 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101666 _25350 _25351 _17984) (@lem1101667 _25350 _25351 f)). Qed.
Lemma lem1101669 {_25350 _25351 : Type'} : (@eq ((list _25351) -> _25350 -> _25350)) = (@eq ((list _25351) -> _25350 -> _25350)).
Proof. exact (eq_refl (@eq ((list _25351) -> _25350 -> _25350))). Qed.
Lemma lem1101670 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term10 _25350 _25351 _17984 f) = (term11 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101669 _25350 _25351) (@lem1101668 _25350 _25351 _17984 f)). Qed.
Lemma lem1101671 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 f)). Qed.
Lemma lem1101672 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : ((term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f)) = ((term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f)).
Proof. exact (MK_COMB (@lem1101670 _25350 _25351 _17984 f) (@lem1101671 _25350 _25351 _17984 f)). Qed.
Lemma lem1101673 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (EQ_MP (@lem1101672 _25350 _25351 _17984 f) (@lem1101664 _25350 _25351 _17984 f)). Qed.
Lemma lem1101674 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term8 _25350 _25351 _17984 f).
Proof. exact (TRANS (@lem1101660 _25350 _25351 f ITLIST' _17984 h1) (@lem1101673 _25350 _25351 _17984 f)). Qed.
Lemma lem1101675 {_25351 : Type'} : (@nil _25351) = (@nil _25351).
Proof. exact (eq_refl (@nil _25351)). Qed.
Lemma lem1101676 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f (@nil _25351)) = (term12 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101674 _25350 _25351 f ITLIST' _17984 h1) (@lem1101675 _25351)). Qed.
Lemma lem1101678 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101679 {_25350 _25351 : Type'} (f : type1152 _25350 _25351) (y : list _25351) : (term13 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101678 (list _25351) (_25350 -> _25350) f y). Qed.
Lemma lem1101680 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term14 _25350 _25351 _17984 f) = (term12 _25350 _25351 _17984 f).
Proof. exact (@lem1101679 _25350 _25351 (term8 _25350 _25351 _17984 f) (@nil _25351)). Qed.
Lemma lem1101681 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17982 : list _25351) (f : type1467 _25350 _25351) : (term15 _25350 _25351 _17984 f _17982) = (term16 _25350 _25351 _17984 _17982 f).
Proof. exact (eq_refl (term15 _25350 _25351 _17984 f _17982)). Qed.
Lemma lem1101682 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term17 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (fun_ext (fun _17982 : list _25351 => @lem1101681 _25350 _25351 _17984 _17982 f)). Qed.
Lemma lem1101683 {_25351 : Type'} : (@nil _25351) = (@nil _25351).
Proof. exact (eq_refl (@nil _25351)). Qed.
Lemma lem1101684 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term14 _25350 _25351 _17984 f) = (term12 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101682 _25350 _25351 _17984 f) (@lem1101683 _25351)). Qed.
Lemma lem1101685 {_25350 : Type'} : (@eq (_25350 -> _25350)) = (@eq (_25350 -> _25350)).
Proof. exact (eq_refl (@eq (_25350 -> _25350))). Qed.
Lemma lem1101686 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term18 _25350 _25351 _17984 f) = (term19 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101685 _25350) (@lem1101684 _25350 _25351 _17984 f)). Qed.
Lemma lem1101687 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term12 _25350 _25351 _17984 f) = (term20 _25350 _25351 _17984 f).
Proof. exact (eq_refl (term12 _25350 _25351 _17984 f)). Qed.
Lemma lem1101688 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : ((term14 _25350 _25351 _17984 f) = (term12 _25350 _25351 _17984 f)) = ((term12 _25350 _25351 _17984 f) = (term20 _25350 _25351 _17984 f)).
Proof. exact (MK_COMB (@lem1101686 _25350 _25351 _17984 f) (@lem1101687 _25350 _25351 _17984 f)). Qed.
Lemma lem1101689 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term12 _25350 _25351 _17984 f) = (term20 _25350 _25351 _17984 f).
Proof. exact (EQ_MP (@lem1101688 _25350 _25351 _17984 f) (@lem1101680 _25350 _25351 _17984 f)). Qed.
Lemma lem1101690 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f (@nil _25351)) = (term20 _25350 _25351 _17984 f).
Proof. exact (TRANS (@lem1101676 _25350 _25351 f ITLIST' _17984 h1) (@lem1101689 _25350 _25351 _17984 f)). Qed.
Lemma lem1101691 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101692 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f (@nil _25351) b) = (term21 _25350 _25351 _17984 f b).
Proof. exact (MK_COMB (@lem1101690 _25350 _25351 f ITLIST' _17984 h1) (@lem1101691 _25350 b)). Qed.
Lemma lem1101694 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101695 {_25350 : Type'} (f : _25350 -> _25350) (y : _25350) : (term22 _25350 f y) = (f y).
Proof. exact (@lem1101694 _25350 _25350 f y). Qed.
Lemma lem1101696 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term23 _25350 _25351 _17984 f b) = (term21 _25350 _25351 _17984 f b).
Proof. exact (@lem1101695 _25350 (term20 _25350 _25351 _17984 f) b). Qed.
Lemma lem1101697 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (_17983 : _25350) : (term21 _25350 _25351 _17984 f _17983) = (_17984 (@nil _25351) f _17983).
Proof. exact (eq_refl (term21 _25350 _25351 _17984 f _17983)). Qed.
Lemma lem1101698 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term24 _25350 _25351 _17984 f) = (term20 _25350 _25351 _17984 f).
Proof. exact (fun_ext (fun _17983 : _25350 => @lem1101697 _25350 _25351 _17984 f _17983)). Qed.
Lemma lem1101699 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101700 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term23 _25350 _25351 _17984 f b) = (term21 _25350 _25351 _17984 f b).
Proof. exact (MK_COMB (@lem1101698 _25350 _25351 _17984 f) (@lem1101699 _25350 b)). Qed.
Lemma lem1101701 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1101702 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term25 _25350 _25351 _17984 f b) = (term26 _25350 _25351 _17984 f b).
Proof. exact (MK_COMB (@lem1101701 _25350) (@lem1101700 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101703 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term21 _25350 _25351 _17984 f b) = (_17984 (@nil _25351) f b).
Proof. exact (eq_refl (term21 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101704 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : ((term23 _25350 _25351 _17984 f b) = (term21 _25350 _25351 _17984 f b)) = ((term21 _25350 _25351 _17984 f b) = (_17984 (@nil _25351) f b)).
Proof. exact (MK_COMB (@lem1101702 _25350 _25351 _17984 f b) (@lem1101703 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101705 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term21 _25350 _25351 _17984 f b) = (_17984 (@nil _25351) f b).
Proof. exact (EQ_MP (@lem1101704 _25350 _25351 _17984 f b) (@lem1101696 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101706 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f (@nil _25351) b) = (_17984 (@nil _25351) f b).
Proof. exact (TRANS (@lem1101692 _25350 _25351 f b ITLIST' _17984 h1) (@lem1101705 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101707 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1101708 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term27 _25350 _25351 ITLIST' f b) = (term28 _25350 _25351 _17984 f b).
Proof. exact (MK_COMB (@lem1101707 _25350) (@lem1101706 _25350 _25351 f b ITLIST' _17984 h1)). Qed.
Lemma lem1101709 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101710 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : ((ITLIST' f (@nil _25351) b) = b) = ((_17984 (@nil _25351) f b) = b).
Proof. exact (MK_COMB (@lem1101708 _25350 _25351 f b ITLIST' _17984 h1) (@lem1101709 _25350 b)). Qed.
Lemma lem1101711 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term29 _25350 _25351 ITLIST' f) = (term30 _25350 _25351 _17984 f).
Proof. exact (fun_ext (fun b : _25350 => @lem1101710 _25350 _25351 f b ITLIST' _17984 h1)). Qed.
Lemma lem1101712 {_25350 : Type'} : (@all _25350) = (@all _25350).
Proof. exact (eq_refl (@all _25350)). Qed.
Lemma lem1101713 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term31 _25350 _25351 ITLIST' f) = (term32 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101712 _25350) (@lem1101711 _25350 _25351 f ITLIST' _17984 h1)). Qed.
Lemma lem1101714 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term33 _25350 _25351 ITLIST') = (term34 _25350 _25351 _17984).
Proof. exact (fun_ext (fun f : type1467 _25350 _25351 => @lem1101713 _25350 _25351 f ITLIST' _17984 h1)). Qed.
Lemma lem1101715 {_25350 _25351 : Type'} : (@all (_25351 -> _25350 -> _25350)) = (@all (_25351 -> _25350 -> _25350)).
Proof. exact (eq_refl (@all (_25351 -> _25350 -> _25350))). Qed.
Lemma lem1101716 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term35 _25350 _25351 ITLIST') = (term36 _25350 _25351 _17984).
Proof. exact (MK_COMB (@lem1101715 _25350 _25351) (@lem1101714 _25350 _25351 ITLIST' _17984 h1)). Qed.
Lemma lem1101717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1101718 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term37 _25350 _25351 ITLIST') = (term38 _25350 _25351 _17984).
Proof. exact (MK_COMB (@lem1101717) (@lem1101716 _25350 _25351 ITLIST' _17984 h1)). Qed.
Lemma lem1101720 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : ITLIST' = (term4 _25350 _25351 _17984).
Proof. exact (h1). Qed.
Lemma lem1101721 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101722 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101720 _25350 _25351 ITLIST' _17984 h1) (@lem1101721 _25350 _25351 f)). Qed.
Lemma lem1101724 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101725 {_25350 _25351 : Type'} (f : type725 _25350 _25351) (y : type1467 _25350 _25351) : (term6 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101724 (type1467 _25350 _25351) (type1152 _25350 _25351) f y). Qed.
Lemma lem1101726 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (@lem1101725 _25350 _25351 (term4 _25350 _25351 _17984) f). Qed.
Lemma lem1101727 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17981 : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 _17981) = (term8 _25350 _25351 _17984 _17981).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101728 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) : (term9 _25350 _25351 _17984) = (term4 _25350 _25351 _17984).
Proof. exact (fun_ext (fun _17981 : type1467 _25350 _25351 => @lem1101727 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101729 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101730 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101728 _25350 _25351 _17984) (@lem1101729 _25350 _25351 f)). Qed.
Lemma lem1101731 {_25350 _25351 : Type'} : (@eq ((list _25351) -> _25350 -> _25350)) = (@eq ((list _25351) -> _25350 -> _25350)).
Proof. exact (eq_refl (@eq ((list _25351) -> _25350 -> _25350))). Qed.
Lemma lem1101732 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term10 _25350 _25351 _17984 f) = (term11 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101731 _25350 _25351) (@lem1101730 _25350 _25351 _17984 f)). Qed.
Lemma lem1101733 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 f)). Qed.
Lemma lem1101734 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : ((term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f)) = ((term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f)).
Proof. exact (MK_COMB (@lem1101732 _25350 _25351 _17984 f) (@lem1101733 _25350 _25351 _17984 f)). Qed.
Lemma lem1101735 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (EQ_MP (@lem1101734 _25350 _25351 _17984 f) (@lem1101726 _25350 _25351 _17984 f)). Qed.
Lemma lem1101736 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term8 _25350 _25351 _17984 f).
Proof. exact (TRANS (@lem1101722 _25350 _25351 f ITLIST' _17984 h1) (@lem1101735 _25350 _25351 _17984 f)). Qed.
Lemma lem1101737 {_25351 : Type'} (h : _25351) (t : list _25351) : (@cons _25351 h t) = (@cons _25351 h t).
Proof. exact (eq_refl (@cons _25351 h t)). Qed.
Lemma lem1101738 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term39 _25350 _25351 ITLIST' f h t) = (term40 _25350 _25351 _17984 f h t).
Proof. exact (MK_COMB (@lem1101736 _25350 _25351 f ITLIST' _17984 h1) (@lem1101737 _25351 h t)). Qed.
Lemma lem1101740 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101741 {_25350 _25351 : Type'} (f : type1152 _25350 _25351) (y : list _25351) : (term13 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101740 (list _25351) (_25350 -> _25350) f y). Qed.
Lemma lem1101742 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) : (term41 _25350 _25351 _17984 f h t) = (term40 _25350 _25351 _17984 f h t).
Proof. exact (@lem1101741 _25350 _25351 (term8 _25350 _25351 _17984 f) (@cons _25351 h t)). Qed.
Lemma lem1101743 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17982 : list _25351) (f : type1467 _25350 _25351) : (term15 _25350 _25351 _17984 f _17982) = (term16 _25350 _25351 _17984 _17982 f).
Proof. exact (eq_refl (term15 _25350 _25351 _17984 f _17982)). Qed.
Lemma lem1101744 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term17 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (fun_ext (fun _17982 : list _25351 => @lem1101743 _25350 _25351 _17984 _17982 f)). Qed.
Lemma lem1101745 {_25351 : Type'} (h : _25351) (t : list _25351) : (@cons _25351 h t) = (@cons _25351 h t).
Proof. exact (eq_refl (@cons _25351 h t)). Qed.
Lemma lem1101746 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) : (term41 _25350 _25351 _17984 f h t) = (term40 _25350 _25351 _17984 f h t).
Proof. exact (MK_COMB (@lem1101744 _25350 _25351 _17984 f) (@lem1101745 _25351 h t)). Qed.
Lemma lem1101747 {_25350 : Type'} : (@eq (_25350 -> _25350)) = (@eq (_25350 -> _25350)).
Proof. exact (eq_refl (@eq (_25350 -> _25350))). Qed.
Lemma lem1101748 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) : (term42 _25350 _25351 _17984 f h t) = (term43 _25350 _25351 _17984 f h t).
Proof. exact (MK_COMB (@lem1101747 _25350) (@lem1101746 _25350 _25351 _17984 f h t)). Qed.
Lemma lem1101749 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term40 _25350 _25351 _17984 f h t) = (term44 _25350 _25351 _17984 h t f).
Proof. exact (eq_refl (term40 _25350 _25351 _17984 f h t)). Qed.
Lemma lem1101750 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) : ((term41 _25350 _25351 _17984 f h t) = (term40 _25350 _25351 _17984 f h t)) = ((term40 _25350 _25351 _17984 f h t) = (term44 _25350 _25351 _17984 h t f)).
Proof. exact (MK_COMB (@lem1101748 _25350 _25351 _17984 f h t) (@lem1101749 _25350 _25351 _17984 h t f)). Qed.
Lemma lem1101751 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term40 _25350 _25351 _17984 f h t) = (term44 _25350 _25351 _17984 h t f).
Proof. exact (EQ_MP (@lem1101750 _25350 _25351 _17984 h t f) (@lem1101742 _25350 _25351 _17984 f h t)). Qed.
Lemma lem1101752 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term39 _25350 _25351 ITLIST' f h t) = (term44 _25350 _25351 _17984 h t f).
Proof. exact (TRANS (@lem1101738 _25350 _25351 f h t ITLIST' _17984 h1) (@lem1101751 _25350 _25351 _17984 h t f)). Qed.
Lemma lem1101753 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101754 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term45 _25350 _25351 ITLIST' f h t b) = (term46 _25350 _25351 _17984 h t f b).
Proof. exact (MK_COMB (@lem1101752 _25350 _25351 h t f ITLIST' _17984 h1) (@lem1101753 _25350 b)). Qed.
Lemma lem1101756 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101757 {_25350 : Type'} (f : _25350 -> _25350) (y : _25350) : (term22 _25350 f y) = (f y).
Proof. exact (@lem1101756 _25350 _25350 f y). Qed.
Lemma lem1101758 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term47 _25350 _25351 _17984 h t f b) = (term46 _25350 _25351 _17984 h t f b).
Proof. exact (@lem1101757 _25350 (term44 _25350 _25351 _17984 h t f) b). Qed.
Lemma lem1101759 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (_17983 : _25350) : (term46 _25350 _25351 _17984 h t f _17983) = (term48 _25350 _25351 _17984 h t f _17983).
Proof. exact (eq_refl (term46 _25350 _25351 _17984 h t f _17983)). Qed.
Lemma lem1101760 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term49 _25350 _25351 _17984 h t f) = (term44 _25350 _25351 _17984 h t f).
Proof. exact (fun_ext (fun _17983 : _25350 => @lem1101759 _25350 _25351 _17984 h t f _17983)). Qed.
Lemma lem1101761 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101762 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term47 _25350 _25351 _17984 h t f b) = (term46 _25350 _25351 _17984 h t f b).
Proof. exact (MK_COMB (@lem1101760 _25350 _25351 _17984 h t f) (@lem1101761 _25350 b)). Qed.
Lemma lem1101763 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1101764 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term50 _25350 _25351 _17984 h t f b) = (term51 _25350 _25351 _17984 h t f b).
Proof. exact (MK_COMB (@lem1101763 _25350) (@lem1101762 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101765 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term46 _25350 _25351 _17984 h t f b) = (term48 _25350 _25351 _17984 h t f b).
Proof. exact (eq_refl (term46 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101766 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : ((term47 _25350 _25351 _17984 h t f b) = (term46 _25350 _25351 _17984 h t f b)) = ((term46 _25350 _25351 _17984 h t f b) = (term48 _25350 _25351 _17984 h t f b)).
Proof. exact (MK_COMB (@lem1101764 _25350 _25351 _17984 h t f b) (@lem1101765 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101767 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term46 _25350 _25351 _17984 h t f b) = (term48 _25350 _25351 _17984 h t f b).
Proof. exact (EQ_MP (@lem1101766 _25350 _25351 _17984 h t f b) (@lem1101758 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101768 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term45 _25350 _25351 ITLIST' f h t b) = (term48 _25350 _25351 _17984 h t f b).
Proof. exact (TRANS (@lem1101754 _25350 _25351 h t f b ITLIST' _17984 h1) (@lem1101767 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101769 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1101770 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term52 _25350 _25351 ITLIST' f h t b) = (term53 _25350 _25351 _17984 h t f b).
Proof. exact (MK_COMB (@lem1101769 _25350) (@lem1101768 _25350 _25351 h t f b ITLIST' _17984 h1)). Qed.
Lemma lem1101772 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : ITLIST' = (term4 _25350 _25351 _17984).
Proof. exact (h1). Qed.
Lemma lem1101773 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101774 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101772 _25350 _25351 ITLIST' _17984 h1) (@lem1101773 _25350 _25351 f)). Qed.
Lemma lem1101776 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101777 {_25350 _25351 : Type'} (f : type725 _25350 _25351) (y : type1467 _25350 _25351) : (term6 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101776 (type1467 _25350 _25351) (type1152 _25350 _25351) f y). Qed.
Lemma lem1101778 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (@lem1101777 _25350 _25351 (term4 _25350 _25351 _17984) f). Qed.
Lemma lem1101779 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17981 : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 _17981) = (term8 _25350 _25351 _17984 _17981).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101780 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) : (term9 _25350 _25351 _17984) = (term4 _25350 _25351 _17984).
Proof. exact (fun_ext (fun _17981 : type1467 _25350 _25351 => @lem1101779 _25350 _25351 _17984 _17981)). Qed.
Lemma lem1101781 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101782 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101780 _25350 _25351 _17984) (@lem1101781 _25350 _25351 f)). Qed.
Lemma lem1101783 {_25350 _25351 : Type'} : (@eq ((list _25351) -> _25350 -> _25350)) = (@eq ((list _25351) -> _25350 -> _25350)).
Proof. exact (eq_refl (@eq ((list _25351) -> _25350 -> _25350))). Qed.
Lemma lem1101784 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term10 _25350 _25351 _17984 f) = (term11 _25350 _25351 _17984 f).
Proof. exact (MK_COMB (@lem1101783 _25350 _25351) (@lem1101782 _25350 _25351 _17984 f)). Qed.
Lemma lem1101785 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (eq_refl (term5 _25350 _25351 _17984 f)). Qed.
Lemma lem1101786 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : ((term7 _25350 _25351 _17984 f) = (term5 _25350 _25351 _17984 f)) = ((term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f)).
Proof. exact (MK_COMB (@lem1101784 _25350 _25351 _17984 f) (@lem1101785 _25350 _25351 _17984 f)). Qed.
Lemma lem1101787 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term5 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (EQ_MP (@lem1101786 _25350 _25351 _17984 f) (@lem1101778 _25350 _25351 _17984 f)). Qed.
Lemma lem1101788 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f) = (term8 _25350 _25351 _17984 f).
Proof. exact (TRANS (@lem1101774 _25350 _25351 f ITLIST' _17984 h1) (@lem1101787 _25350 _25351 _17984 f)). Qed.
Lemma lem1101789 {_25351 : Type'} (t : list _25351) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1101790 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (t : list _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f t) = (term15 _25350 _25351 _17984 f t).
Proof. exact (MK_COMB (@lem1101788 _25350 _25351 f ITLIST' _17984 h1) (@lem1101789 _25351 t)). Qed.
Lemma lem1101792 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101793 {_25350 _25351 : Type'} (f : type1152 _25350 _25351) (y : list _25351) : (term13 _25350 _25351 f y) = (f y).
Proof. exact (@lem1101792 (list _25351) (_25350 -> _25350) f y). Qed.
Lemma lem1101794 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term54 _25350 _25351 _17984 f t) = (term15 _25350 _25351 _17984 f t).
Proof. exact (@lem1101793 _25350 _25351 (term8 _25350 _25351 _17984 f) t). Qed.
Lemma lem1101795 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (_17982 : list _25351) (f : type1467 _25350 _25351) : (term15 _25350 _25351 _17984 f _17982) = (term16 _25350 _25351 _17984 _17982 f).
Proof. exact (eq_refl (term15 _25350 _25351 _17984 f _17982)). Qed.
Lemma lem1101796 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term17 _25350 _25351 _17984 f) = (term8 _25350 _25351 _17984 f).
Proof. exact (fun_ext (fun _17982 : list _25351 => @lem1101795 _25350 _25351 _17984 _17982 f)). Qed.
Lemma lem1101797 {_25351 : Type'} (t : list _25351) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1101798 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term54 _25350 _25351 _17984 f t) = (term15 _25350 _25351 _17984 f t).
Proof. exact (MK_COMB (@lem1101796 _25350 _25351 _17984 f) (@lem1101797 _25351 t)). Qed.
Lemma lem1101799 {_25350 : Type'} : (@eq (_25350 -> _25350)) = (@eq (_25350 -> _25350)).
Proof. exact (eq_refl (@eq (_25350 -> _25350))). Qed.
Lemma lem1101800 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term55 _25350 _25351 _17984 f t) = (term56 _25350 _25351 _17984 f t).
Proof. exact (MK_COMB (@lem1101799 _25350) (@lem1101798 _25350 _25351 _17984 f t)). Qed.
Lemma lem1101801 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term15 _25350 _25351 _17984 f t) = (term16 _25350 _25351 _17984 t f).
Proof. exact (eq_refl (term15 _25350 _25351 _17984 f t)). Qed.
Lemma lem1101802 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : ((term54 _25350 _25351 _17984 f t) = (term15 _25350 _25351 _17984 f t)) = ((term15 _25350 _25351 _17984 f t) = (term16 _25350 _25351 _17984 t f)).
Proof. exact (MK_COMB (@lem1101800 _25350 _25351 _17984 f t) (@lem1101801 _25350 _25351 _17984 t f)). Qed.
Lemma lem1101803 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term15 _25350 _25351 _17984 f t) = (term16 _25350 _25351 _17984 t f).
Proof. exact (EQ_MP (@lem1101802 _25350 _25351 _17984 t f) (@lem1101794 _25350 _25351 _17984 f t)). Qed.
Lemma lem1101804 {_25350 _25351 : Type'} (t : list _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f t) = (term16 _25350 _25351 _17984 t f).
Proof. exact (TRANS (@lem1101790 _25350 _25351 f t ITLIST' _17984 h1) (@lem1101803 _25350 _25351 _17984 t f)). Qed.
Lemma lem1101805 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101806 {_25350 _25351 : Type'} (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f t b) = (term57 _25350 _25351 _17984 t f b).
Proof. exact (MK_COMB (@lem1101804 _25350 _25351 t f ITLIST' _17984 h1) (@lem1101805 _25350 b)). Qed.
Lemma lem1101808 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1101655 A B f y) (@lem1101654 A B f y)). Qed.
Lemma lem1101809 {_25350 : Type'} (f : _25350 -> _25350) (y : _25350) : (term22 _25350 f y) = (f y).
Proof. exact (@lem1101808 _25350 _25350 f y). Qed.
Lemma lem1101810 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term58 _25350 _25351 _17984 t f b) = (term57 _25350 _25351 _17984 t f b).
Proof. exact (@lem1101809 _25350 (term16 _25350 _25351 _17984 t f) b). Qed.
Lemma lem1101811 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (_17983 : _25350) : (term57 _25350 _25351 _17984 t f _17983) = (_17984 t f _17983).
Proof. exact (eq_refl (term57 _25350 _25351 _17984 t f _17983)). Qed.
Lemma lem1101812 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term59 _25350 _25351 _17984 t f) = (term16 _25350 _25351 _17984 t f).
Proof. exact (fun_ext (fun _17983 : _25350 => @lem1101811 _25350 _25351 _17984 t f _17983)). Qed.
Lemma lem1101813 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101814 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term58 _25350 _25351 _17984 t f b) = (term57 _25350 _25351 _17984 t f b).
Proof. exact (MK_COMB (@lem1101812 _25350 _25351 _17984 t f) (@lem1101813 _25350 b)). Qed.
Lemma lem1101815 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1101816 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term60 _25350 _25351 _17984 t f b) = (term61 _25350 _25351 _17984 t f b).
Proof. exact (MK_COMB (@lem1101815 _25350) (@lem1101814 _25350 _25351 _17984 t f b)). Qed.
Lemma lem1101817 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term57 _25350 _25351 _17984 t f b) = (_17984 t f b).
Proof. exact (eq_refl (term57 _25350 _25351 _17984 t f b)). Qed.
Lemma lem1101818 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : ((term58 _25350 _25351 _17984 t f b) = (term57 _25350 _25351 _17984 t f b)) = ((term57 _25350 _25351 _17984 t f b) = (_17984 t f b)).
Proof. exact (MK_COMB (@lem1101816 _25350 _25351 _17984 t f b) (@lem1101817 _25350 _25351 _17984 t f b)). Qed.
Lemma lem1101819 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term57 _25350 _25351 _17984 t f b) = (_17984 t f b).
Proof. exact (EQ_MP (@lem1101818 _25350 _25351 _17984 t f b) (@lem1101810 _25350 _25351 _17984 t f b)). Qed.
Lemma lem1101820 {_25350 _25351 : Type'} (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (ITLIST' f t b) = (_17984 t f b).
Proof. exact (TRANS (@lem1101806 _25350 _25351 t f b ITLIST' _17984 h1) (@lem1101819 _25350 _25351 _17984 t f b)). Qed.
Lemma lem1101821 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) : (f h) = (f h).
Proof. exact (eq_refl (f h)). Qed.
Lemma lem1101822 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term62 _25350 _25351 h ITLIST' f t b) = (term63 _25350 _25351 h _17984 t f b).
Proof. exact (MK_COMB (@lem1101821 _25350 _25351 f h) (@lem1101820 _25350 _25351 t f b ITLIST' _17984 h1)). Qed.
Lemma lem1101823 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : ((term45 _25350 _25351 ITLIST' f h t b) = (term62 _25350 _25351 h ITLIST' f t b)) = ((term48 _25350 _25351 _17984 h t f b) = (term63 _25350 _25351 h _17984 t f b)).
Proof. exact (MK_COMB (@lem1101770 _25350 _25351 h t f b ITLIST' _17984 h1) (@lem1101822 _25350 _25351 h t f b ITLIST' _17984 h1)). Qed.
Lemma lem1101824 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term64 _25350 _25351 h ITLIST' f t) = (term65 _25350 _25351 h _17984 t f).
Proof. exact (fun_ext (fun b : _25350 => @lem1101823 _25350 _25351 h t f b ITLIST' _17984 h1)). Qed.
Lemma lem1101825 {_25350 : Type'} : (@all _25350) = (@all _25350).
Proof. exact (eq_refl (@all _25350)). Qed.
Lemma lem1101826 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term66 _25350 _25351 h ITLIST' f t) = (term67 _25350 _25351 h _17984 t f).
Proof. exact (MK_COMB (@lem1101825 _25350) (@lem1101824 _25350 _25351 h t f ITLIST' _17984 h1)). Qed.
Lemma lem1101827 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term68 _25350 _25351 h ITLIST' f) = (term69 _25350 _25351 h _17984 f).
Proof. exact (fun_ext (fun t : list _25351 => @lem1101826 _25350 _25351 h t f ITLIST' _17984 h1)). Qed.
Lemma lem1101828 {_25351 : Type'} : (@all (list _25351)) = (@all (list _25351)).
Proof. exact (eq_refl (@all (list _25351))). Qed.
Lemma lem1101829 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term70 _25350 _25351 h ITLIST' f) = (term71 _25350 _25351 h _17984 f).
Proof. exact (MK_COMB (@lem1101828 _25351) (@lem1101827 _25350 _25351 h f ITLIST' _17984 h1)). Qed.
Lemma lem1101830 {_25350 _25351 : Type'} (h : _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term72 _25350 _25351 h ITLIST') = (term73 _25350 _25351 h _17984).
Proof. exact (fun_ext (fun f : type1467 _25350 _25351 => @lem1101829 _25350 _25351 h f ITLIST' _17984 h1)). Qed.
Lemma lem1101831 {_25350 _25351 : Type'} : (@all (_25351 -> _25350 -> _25350)) = (@all (_25351 -> _25350 -> _25350)).
Proof. exact (eq_refl (@all (_25351 -> _25350 -> _25350))). Qed.
Lemma lem1101832 {_25350 _25351 : Type'} (h : _25351) (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term74 _25350 _25351 h ITLIST') = (term75 _25350 _25351 h _17984).
Proof. exact (MK_COMB (@lem1101831 _25350 _25351) (@lem1101830 _25350 _25351 h ITLIST' _17984 h1)). Qed.
Lemma lem1101833 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term76 _25350 _25351 ITLIST') = (term77 _25350 _25351 _17984).
Proof. exact (fun_ext (fun h : _25351 => @lem1101832 _25350 _25351 h ITLIST' _17984 h1)). Qed.
Lemma lem1101834 {_25351 : Type'} : (@all _25351) = (@all _25351).
Proof. exact (eq_refl (@all _25351)). Qed.
Lemma lem1101835 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term78 _25350 _25351 ITLIST') = (term79 _25350 _25351 _17984).
Proof. exact (MK_COMB (@lem1101834 _25351) (@lem1101833 _25350 _25351 ITLIST' _17984 h1)). Qed.
Lemma lem1101836 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term80 _25350 _25351 ITLIST') = (term81 _25350 _25351 _17984).
Proof. exact (MK_COMB (@lem1101718 _25350 _25351 ITLIST' _17984 h1) (@lem1101835 _25350 _25351 ITLIST' _17984 h1)). Qed.
Lemma lem1101837 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : (_17984 (@nil _25351)) = (term82 _25350 _25351).
Proof. exact (h1). Qed.
Lemma lem1101838 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101839 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : (_17984 (@nil _25351) f) = (term83 _25350 _25351 f).
Proof. exact (MK_COMB (@lem1101837 _25350 _25351 _17984 h1) (@lem1101838 _25350 _25351 f)). Qed.
Lemma lem1101840 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term83 _25350 _25351 f) = (term84 _25350).
Proof. exact (eq_refl (term83 _25350 _25351 f)). Qed.
Lemma lem1101841 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : (term85 _25350 _25351 _17984 f) = (term85 _25350 _25351 _17984 f).
Proof. exact (eq_refl (term85 _25350 _25351 _17984 f)). Qed.
Lemma lem1101842 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) : ((_17984 (@nil _25351) f) = (term83 _25350 _25351 f)) = ((_17984 (@nil _25351) f) = (term84 _25350)).
Proof. exact (MK_COMB (@lem1101841 _25350 _25351 _17984 f) (@lem1101840 _25350 _25351 f)). Qed.
Lemma lem1101843 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : (_17984 (@nil _25351) f) = (term84 _25350).
Proof. exact (EQ_MP (@lem1101842 _25350 _25351 _17984 f) (@lem1101839 _25350 _25351 f _17984 h1)). Qed.
Lemma lem1101844 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101845 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : (_17984 (@nil _25351) f b) = (term86 _25350 b).
Proof. exact (MK_COMB (@lem1101843 _25350 _25351 f _17984 h1) (@lem1101844 _25350 b)). Qed.
Lemma lem1101846 {_25350 : Type'} (b : _25350) : (term86 _25350 b) = b.
Proof. exact (eq_refl (term86 _25350 b)). Qed.
Lemma lem1101847 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : (term28 _25350 _25351 _17984 f b) = (term28 _25350 _25351 _17984 f b).
Proof. exact (eq_refl (term28 _25350 _25351 _17984 f b)). Qed.
Lemma lem1101848 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (f : type1467 _25350 _25351) (b : _25350) : ((_17984 (@nil _25351) f b) = (term86 _25350 b)) = ((_17984 (@nil _25351) f b) = b).
Proof. exact (MK_COMB (@lem1101847 _25350 _25351 _17984 f b) (@lem1101846 _25350 b)). Qed.
Lemma lem1101849 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : (_17984 (@nil _25351) f b) = b.
Proof. exact (EQ_MP (@lem1101848 _25350 _25351 _17984 f b) (@lem1101845 _25350 _25351 f b _17984 h1)). Qed.
Lemma lem1101850 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : term32 _25350 _25351 _17984 f.
Proof. exact (fun b : _25350 => @lem1101849 _25350 _25351 f b _17984 h1). Qed.
Lemma lem1101851 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : (_17984 (@nil _25351)) = (term82 _25350 _25351)) : term36 _25350 _25351 _17984.
Proof. exact (fun f : type1467 _25350 _25351 => @lem1101850 _25350 _25351 f _17984 h1). Qed.
Lemma lem1101852 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term87 _25350 _25351 _17984.
Proof. exact (h1). Qed.
Lemma lem1101853 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term88 _25350 _25351 _17984 h.
Proof. exact (@lem1101852 _25350 _25351 _17984 h1 h). Qed.
Lemma lem1101854 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) : (term88 _25350 _25351 _17984 h) = (term89 _25350 _25351 h _17984).
Proof. exact (eq_refl (term88 _25350 _25351 _17984 h)). Qed.
Lemma lem1101855 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term89 _25350 _25351 h _17984.
Proof. exact (EQ_MP (@lem1101854 _25350 _25351 h _17984) (@lem1101853 _25350 _25351 h _17984 h1)). Qed.
Lemma lem1101856 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term90 _25350 _25351 h _17984 t.
Proof. exact (@lem1101855 _25350 _25351 h _17984 h1 t). Qed.
Lemma lem1101857 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (t : list _25351) : (term90 _25350 _25351 h _17984 t) = ((term91 _25350 _25351 _17984 h t) = (term92 _25350 _25351 h _17984 t)).
Proof. exact (eq_refl (term90 _25350 _25351 h _17984 t)). Qed.
Lemma lem1101858 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : (term91 _25350 _25351 _17984 h t) = (term92 _25350 _25351 h _17984 t).
Proof. exact (EQ_MP (@lem1101857 _25350 _25351 h _17984 t) (@lem1101856 _25350 _25351 h t _17984 h1)). Qed.
Lemma lem1101859 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1101860 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : (term93 _25350 _25351 _17984 h t f) = (term94 _25350 _25351 h _17984 t f).
Proof. exact (MK_COMB (@lem1101858 _25350 _25351 h t _17984 h1) (@lem1101859 _25350 _25351 f)). Qed.
Lemma lem1101861 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term94 _25350 _25351 h _17984 t f) = (term95 _25350 _25351 h _17984 t f).
Proof. exact (eq_refl (term94 _25350 _25351 h _17984 t f)). Qed.
Lemma lem1101862 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) : (term96 _25350 _25351 _17984 h t f) = (term96 _25350 _25351 _17984 h t f).
Proof. exact (eq_refl (term96 _25350 _25351 _17984 h t f)). Qed.
Lemma lem1101863 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) : ((term93 _25350 _25351 _17984 h t f) = (term94 _25350 _25351 h _17984 t f)) = ((term93 _25350 _25351 _17984 h t f) = (term95 _25350 _25351 h _17984 t f)).
Proof. exact (MK_COMB (@lem1101862 _25350 _25351 _17984 h t f) (@lem1101861 _25350 _25351 h _17984 t f)). Qed.
Lemma lem1101864 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : (term93 _25350 _25351 _17984 h t f) = (term95 _25350 _25351 h _17984 t f).
Proof. exact (EQ_MP (@lem1101863 _25350 _25351 h _17984 t f) (@lem1101860 _25350 _25351 h t f _17984 h1)). Qed.
Lemma lem1101865 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1101866 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : (term48 _25350 _25351 _17984 h t f b) = (term97 _25350 _25351 h _17984 t f b).
Proof. exact (MK_COMB (@lem1101864 _25350 _25351 h t f _17984 h1) (@lem1101865 _25350 b)). Qed.
Lemma lem1101867 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term97 _25350 _25351 h _17984 t f b) = (term63 _25350 _25351 h _17984 t f b).
Proof. exact (eq_refl (term97 _25350 _25351 h _17984 t f b)). Qed.
Lemma lem1101868 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : (term53 _25350 _25351 _17984 h t f b) = (term53 _25350 _25351 _17984 h t f b).
Proof. exact (eq_refl (term53 _25350 _25351 _17984 h t f b)). Qed.
Lemma lem1101869 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) : ((term48 _25350 _25351 _17984 h t f b) = (term97 _25350 _25351 h _17984 t f b)) = ((term48 _25350 _25351 _17984 h t f b) = (term63 _25350 _25351 h _17984 t f b)).
Proof. exact (MK_COMB (@lem1101868 _25350 _25351 _17984 h t f b) (@lem1101867 _25350 _25351 h _17984 t f b)). Qed.
Lemma lem1101870 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (b : _25350) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : (term48 _25350 _25351 _17984 h t f b) = (term63 _25350 _25351 h _17984 t f b).
Proof. exact (EQ_MP (@lem1101869 _25350 _25351 h _17984 t f b) (@lem1101866 _25350 _25351 h t f b _17984 h1)). Qed.
Lemma lem1101871 {_25350 _25351 : Type'} (h : _25351) (t : list _25351) (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term67 _25350 _25351 h _17984 t f.
Proof. exact (fun b : _25350 => @lem1101870 _25350 _25351 h t f b _17984 h1). Qed.
Lemma lem1101872 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term71 _25350 _25351 h _17984 f.
Proof. exact (fun t : list _25351 => @lem1101871 _25350 _25351 h t f _17984 h1). Qed.
Lemma lem1101873 {_25350 _25351 : Type'} (h : _25351) (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term75 _25350 _25351 h _17984.
Proof. exact (fun f : type1467 _25350 _25351 => @lem1101872 _25350 _25351 h f _17984 h1). Qed.
Lemma lem1101874 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term87 _25350 _25351 _17984) : term79 _25350 _25351 _17984.
Proof. exact (fun h : _25351 => @lem1101873 _25350 _25351 h _17984 h1). Qed.
Lemma lem1101875 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term98 _25350 _25351 _17984.
Proof. exact (h1). Qed.
Lemma lem1101876 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term87 _25350 _25351 _17984.
Proof. exact (proj2 (@lem1101875 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101877 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : (_17984 (@nil _25351)) = (term82 _25350 _25351).
Proof. exact (proj1 (@lem1101875 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101878 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : ((_17984 (@nil _25351)) = (term82 _25350 _25351)) = (term36 _25350 _25351 _17984).
Proof. exact (prop_ext (fun h2 : (_17984 (@nil _25351)) = (term82 _25350 _25351) => @lem1101851 _25350 _25351 _17984 h2) (fun h2 : term36 _25350 _25351 _17984 => @lem1101877 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101879 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term36 _25350 _25351 _17984.
Proof. exact (EQ_MP (@lem1101878 _25350 _25351 _17984 h1) (@lem1101877 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101880 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : (term87 _25350 _25351 _17984) = (term79 _25350 _25351 _17984).
Proof. exact (prop_ext (fun h2 : term87 _25350 _25351 _17984 => @lem1101874 _25350 _25351 _17984 h2) (fun h2 : term79 _25350 _25351 _17984 => @lem1101876 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101881 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term79 _25350 _25351 _17984.
Proof. exact (EQ_MP (@lem1101880 _25350 _25351 _17984 h1) (@lem1101876 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101882 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term81 _25350 _25351 _17984.
Proof. exact (conj (@lem1101879 _25350 _25351 _17984 h1) (@lem1101881 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101883 {A Z : Type'} (NIL' : Z) : term99 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1101884 {A Z : Type'} (NIL' : Z) : (term99 A Z NIL') = (term100 A Z NIL').
Proof. exact (eq_refl (term99 A Z NIL')). Qed.
Lemma lem1101885 {A Z : Type'} (NIL' : Z) : term100 A Z NIL'.
Proof. exact (EQ_MP (@lem1101884 A Z NIL') (@lem1101883 A Z NIL')). Qed.
Lemma lem1101886 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term101 A Z NIL' CONS'.
Proof. exact (@lem1101885 A Z NIL' CONS'). Qed.
Lemma lem1101887 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term101 A Z NIL' CONS') = (term102 A Z NIL' CONS').
Proof. exact (eq_refl (term101 A Z NIL' CONS')). Qed.
Lemma lem1101888 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term102 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1101887 A Z NIL' CONS') (@lem1101886 A Z NIL' CONS')). Qed.
Lemma lem1101889 {_25350 _25351 : Type'} (NIL' : type726 _25350 _25351) (CONS' : type1458 _25350 _25351) : term103 _25350 _25351 NIL' CONS'.
Proof. exact (@lem1101888 _25351 (type726 _25350 _25351) NIL' CONS'). Qed.
Lemma lem1101890 {_25350 _25351 : Type'} : term104 _25350 _25351.
Proof. exact (@lem1101889 _25350 _25351 (term82 _25350 _25351) (term105 _25350 _25351)). Qed.
Lemma lem1101891 {_25350 _25351 : Type'} (a0 : _25351) : (term106 _25350 _25351 a0) = (term107 _25350 _25351 a0).
Proof. exact (eq_refl (term106 _25350 _25351 a0)). Qed.
Lemma lem1101892 {_25351 : Type'} (a1 : list _25351) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1101893 {_25350 _25351 : Type'} (a0 : _25351) (a1 : list _25351) : (term108 _25350 _25351 a0 a1) = (term109 _25350 _25351 a0 a1).
Proof. exact (MK_COMB (@lem1101891 _25350 _25351 a0) (@lem1101892 _25351 a1)). Qed.
Lemma lem1101894 {_25350 _25351 : Type'} (a1 : list _25351) (a0 : _25351) : (term109 _25350 _25351 a0 a1) = (term110 _25350 _25351 a0).
Proof. exact (eq_refl (term109 _25350 _25351 a0 a1)). Qed.
Lemma lem1101895 {_25350 _25351 : Type'} (a1 : list _25351) (a0 : _25351) : (term108 _25350 _25351 a0 a1) = (term110 _25350 _25351 a0).
Proof. exact (TRANS (@lem1101893 _25350 _25351 a0 a1) (@lem1101894 _25350 _25351 a1 a0)). Qed.
Lemma lem1101896 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) (a1 : list _25351) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1101897 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) (a1 : list _25351) : (term111 _25350 _25351 a0 fn a1) = (term112 _25350 _25351 a0 fn a1).
Proof. exact (MK_COMB (@lem1101895 _25350 _25351 a1 a0) (@lem1101896 _25350 _25351 fn a1)). Qed.
Lemma lem1101898 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) (a1 : list _25351) : (term112 _25350 _25351 a0 fn a1) = (term92 _25350 _25351 a0 fn a1).
Proof. exact (eq_refl (term112 _25350 _25351 a0 fn a1)). Qed.
Lemma lem1101899 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) (a1 : list _25351) : (term111 _25350 _25351 a0 fn a1) = (term92 _25350 _25351 a0 fn a1).
Proof. exact (TRANS (@lem1101897 _25350 _25351 a0 fn a1) (@lem1101898 _25350 _25351 a0 fn a1)). Qed.
Lemma lem1101900 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) (a0 : _25351) (a1 : list _25351) : (term113 _25350 _25351 fn a0 a1) = (term113 _25350 _25351 fn a0 a1).
Proof. exact (eq_refl (term113 _25350 _25351 fn a0 a1)). Qed.
Lemma lem1101901 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) (a1 : list _25351) : ((term91 _25350 _25351 fn a0 a1) = (term111 _25350 _25351 a0 fn a1)) = ((term91 _25350 _25351 fn a0 a1) = (term92 _25350 _25351 a0 fn a1)).
Proof. exact (MK_COMB (@lem1101900 _25350 _25351 fn a0 a1) (@lem1101899 _25350 _25351 a0 fn a1)). Qed.
Lemma lem1101902 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) : (term114 _25350 _25351 a0 fn) = (term115 _25350 _25351 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25351 => @lem1101901 _25350 _25351 a0 fn a1)). Qed.
Lemma lem1101903 {_25351 : Type'} : (@all (list _25351)) = (@all (list _25351)).
Proof. exact (eq_refl (@all (list _25351))). Qed.
Lemma lem1101904 {_25350 _25351 : Type'} (a0 : _25351) (fn : type1145 _25350 _25351) : (term116 _25350 _25351 a0 fn) = (term89 _25350 _25351 a0 fn).
Proof. exact (MK_COMB (@lem1101903 _25351) (@lem1101902 _25350 _25351 a0 fn)). Qed.
Lemma lem1101905 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) : (term117 _25350 _25351 fn) = (term118 _25350 _25351 fn).
Proof. exact (fun_ext (fun a0 : _25351 => @lem1101904 _25350 _25351 a0 fn)). Qed.
Lemma lem1101906 {_25351 : Type'} : (@all _25351) = (@all _25351).
Proof. exact (eq_refl (@all _25351)). Qed.
Lemma lem1101907 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) : (term119 _25350 _25351 fn) = (term87 _25350 _25351 fn).
Proof. exact (MK_COMB (@lem1101906 _25351) (@lem1101905 _25350 _25351 fn)). Qed.
Lemma lem1101908 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) : (term120 _25350 _25351 fn) = (term120 _25350 _25351 fn).
Proof. exact (eq_refl (term120 _25350 _25351 fn)). Qed.
Lemma lem1101909 {_25350 _25351 : Type'} (fn : type1145 _25350 _25351) : (term121 _25350 _25351 fn) = (term98 _25350 _25351 fn).
Proof. exact (MK_COMB (@lem1101908 _25350 _25351 fn) (@lem1101907 _25350 _25351 fn)). Qed.
Lemma lem1101910 {_25350 _25351 : Type'} : (term122 _25350 _25351) = (term123 _25350 _25351).
Proof. exact (fun_ext (fun fn : type1145 _25350 _25351 => @lem1101909 _25350 _25351 fn)). Qed.
Lemma lem1101911 {_25350 _25351 : Type'} : (@ex ((list _25351) -> (_25351 -> _25350 -> _25350) -> _25350 -> _25350)) = (@ex ((list _25351) -> (_25351 -> _25350 -> _25350) -> _25350 -> _25350)).
Proof. exact (eq_refl (@ex ((list _25351) -> (_25351 -> _25350 -> _25350) -> _25350 -> _25350))). Qed.
Lemma lem1101912 {_25350 _25351 : Type'} : (term104 _25350 _25351) = (term124 _25350 _25351).
Proof. exact (MK_COMB (@lem1101911 _25350 _25351) (@lem1101910 _25350 _25351)). Qed.
Lemma lem1101913 {_25350 _25351 : Type'} : term124 _25350 _25351.
Proof. exact (EQ_MP (@lem1101912 _25350 _25351) (@lem1101890 _25350 _25351)). Qed.
Lemma lem1101914 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term98 _25350 _25351 _17984.
Proof. exact (h1). Qed.
Lemma lem1101915 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term87 _25350 _25351 _17984.
Proof. exact (proj2 (@lem1101914 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101916 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : (_17984 (@nil _25351)) = (term82 _25350 _25351).
Proof. exact (proj1 (@lem1101914 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101917 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term98 _25350 _25351 _17984.
Proof. exact (conj (@lem1101916 _25350 _25351 _17984 h1) (@lem1101915 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101918 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term124 _25350 _25351.
Proof. exact (ex_intro (term123 _25350 _25351) _17984 (@lem1101917 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101919 {_25350 _25351 : Type'} (h1 : term124 _25350 _25351) : term124 _25350 _25351.
Proof. exact (h1). Qed.
Lemma lem1101920 {_25350 _25351 : Type'} (h1 : term124 _25350 _25351) : term124 _25350 _25351.
Proof. exact (ex_elim (@lem1101919 _25350 _25351 h1) (fun _17984 : type1145 _25350 _25351 => fun h0 : term123 _25350 _25351 _17984 => @lem1101918 _25350 _25351 _17984 h0)). Qed.
Lemma lem1101921 {_25350 _25351 : Type'} : (term124 _25350 _25351) = (term124 _25350 _25351).
Proof. exact (prop_ext (fun h1 : term124 _25350 _25351 => @lem1101920 _25350 _25351 h1) (fun h1 : term124 _25350 _25351 => @lem1101913 _25350 _25351)). Qed.
Lemma lem1101922 {_25350 _25351 : Type'} : term124 _25350 _25351.
Proof. exact (EQ_MP (@lem1101921 _25350 _25351) (@lem1101913 _25350 _25351)). Qed.
Lemma lem1101923 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term98 _25350 _25351 _17984) : term125 _25350 _25351.
Proof. exact (ex_intro (term126 _25350 _25351) _17984 (@lem1101882 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101924 {_25350 _25351 : Type'} (h1 : term124 _25350 _25351) : term124 _25350 _25351.
Proof. exact (h1). Qed.
Lemma lem1101925 {_25350 _25351 : Type'} (h1 : term124 _25350 _25351) : term125 _25350 _25351.
Proof. exact (ex_elim (@lem1101924 _25350 _25351 h1) (fun _17984 : type1145 _25350 _25351 => fun h0 : term123 _25350 _25351 _17984 => @lem1101923 _25350 _25351 _17984 h0)). Qed.
Lemma lem1101926 {_25350 _25351 : Type'} : (term124 _25350 _25351) = (term125 _25350 _25351).
Proof. exact (prop_ext (fun h1 : term124 _25350 _25351 => @lem1101925 _25350 _25351 h1) (fun h1 : term125 _25350 _25351 => @lem1101922 _25350 _25351)). Qed.
Lemma lem1101927 {_25350 _25351 : Type'} : term125 _25350 _25351.
Proof. exact (EQ_MP (@lem1101926 _25350 _25351) (@lem1101922 _25350 _25351)). Qed.
Lemma lem1101928 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) : term81 _25350 _25351 _17984.
Proof. exact (h1). Qed.
Lemma lem1101929 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : ITLIST' = (term4 _25350 _25351 _17984)) : (term81 _25350 _25351 _17984) = (term80 _25350 _25351 ITLIST').
Proof. exact (SYM (@lem1101836 _25350 _25351 ITLIST' _17984 h1)). Qed.
Lemma lem1101930 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) (h2 : ITLIST' = (term4 _25350 _25351 _17984)) : term80 _25350 _25351 ITLIST'.
Proof. exact (EQ_MP (@lem1101929 _25350 _25351 ITLIST' _17984 h2) (@lem1101928 _25350 _25351 _17984 h1)). Qed.
Lemma lem1101931 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) (h2 : ITLIST' = (term4 _25350 _25351 _17984)) : term127 _25350 _25351.
Proof. exact (ex_intro (term128 _25350 _25351) ITLIST' (@lem1101930 _25350 _25351 ITLIST' _17984 h1 h2)). Qed.
Lemma lem1101932 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) : (term4 _25350 _25351 _17984) = (term4 _25350 _25351 _17984).
Proof. exact (eq_refl (term4 _25350 _25351 _17984)). Qed.
Lemma lem1101933 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) : term129 _25350 _25351 ITLIST' _17984.
Proof. exact (fun h0 : ITLIST' = (term4 _25350 _25351 _17984) => @lem1101931 _25350 _25351 ITLIST' _17984 h1 h0). Qed.
Lemma lem1101934 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) : term130 _25350 _25351 _17984.
Proof. exact (@lem1101933 _25350 _25351 (term4 _25350 _25351 _17984) _17984 h1). Qed.
Lemma lem1101935 {_25350 _25351 : Type'} (_17984 : type1145 _25350 _25351) (h1 : term81 _25350 _25351 _17984) : term127 _25350 _25351.
Proof. exact (@lem1101934 _25350 _25351 _17984 h1 (@lem1101932 _25350 _25351 _17984)). Qed.
Lemma lem1101936 {_25350 _25351 : Type'} (h1 : term125 _25350 _25351) : term125 _25350 _25351.
Proof. exact (h1). Qed.
Lemma lem1101937 {_25350 _25351 : Type'} (h1 : term125 _25350 _25351) : term127 _25350 _25351.
Proof. exact (ex_elim (@lem1101936 _25350 _25351 h1) (fun _17984 : type1145 _25350 _25351 => fun h0 : term126 _25350 _25351 _17984 => @lem1101935 _25350 _25351 _17984 h0)). Qed.
Lemma lem1101938 {_25350 _25351 : Type'} : (term125 _25350 _25351) = (term127 _25350 _25351).
Proof. exact (prop_ext (fun h1 : term125 _25350 _25351 => @lem1101937 _25350 _25351 h1) (fun h1 : term127 _25350 _25351 => @lem1101927 _25350 _25351)). Qed.
Lemma lem1101939 {_25350 _25351 : Type'} : term127 _25350 _25351.
Proof. exact (EQ_MP (@lem1101938 _25350 _25351) (@lem1101927 _25350 _25351)). Qed.
Lemma lem1101940 {_25350 _25351 : Type'} : term131 _25350 _25351.
Proof. exact (fun _17988 : type1671 => @lem1101939 _25350 _25351). Qed.
Lemma lem1101941 {A B : Type'} (P : type1413 A B) : term132 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1101942 {A B : Type'} (P : type1413 A B) : (term132 A B P) = ((term133 A B P) = (term134 A B P)).
Proof. exact (eq_refl (term132 A B P)). Qed.
Lemma lem1101945 {A B : Type'} (P : type1413 A B) : (term133 A B P) = (term134 A B P).
Proof. exact (EQ_MP (@lem1101942 A B P) (@lem1101941 A B P)). Qed.
Lemma lem1101946 {_25350 _25351 : Type'} (P : type1263 _25350 _25351) : (term135 _25350 _25351 P) = (term136 _25350 _25351 P).
Proof. exact (@lem1101945 type1671 (type725 _25350 _25351) P). Qed.
Lemma lem1101947 {_25350 _25351 : Type'} : (term137 _25350 _25351) = (term138 _25350 _25351).
Proof. exact (@lem1101946 _25350 _25351 (term139 _25350 _25351)). Qed.
Lemma lem1101948 {_25350 _25351 : Type'} (_17988 : type1671) : (term140 _25350 _25351 _17988) = (term128 _25350 _25351).
Proof. exact (eq_refl (term140 _25350 _25351 _17988)). Qed.
Lemma lem1101949 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) : ITLIST' = ITLIST'.
Proof. exact (eq_refl ITLIST'). Qed.
Lemma lem1101950 {_25350 _25351 : Type'} (_17988 : type1671) (ITLIST' : type725 _25350 _25351) : (term141 _25350 _25351 _17988 ITLIST') = (term142 _25350 _25351 ITLIST').
Proof. exact (MK_COMB (@lem1101948 _25350 _25351 _17988) (@lem1101949 _25350 _25351 ITLIST')). Qed.
Lemma lem1101951 {_25350 _25351 : Type'} (ITLIST' : type725 _25350 _25351) : (term142 _25350 _25351 ITLIST') = (term80 _25350 _25351 ITLIST').
Proof. exact (eq_refl (term142 _25350 _25351 ITLIST')). Qed.
Lemma lem1101952 {_25350 _25351 : Type'} (_17988 : type1671) (ITLIST' : type725 _25350 _25351) : (term141 _25350 _25351 _17988 ITLIST') = (term80 _25350 _25351 ITLIST').
Proof. exact (TRANS (@lem1101950 _25350 _25351 _17988 ITLIST') (@lem1101951 _25350 _25351 ITLIST')). Qed.
Lemma lem1101953 {_25350 _25351 : Type'} (_17988 : type1671) : (term143 _25350 _25351 _17988) = (term128 _25350 _25351).
Proof. exact (fun_ext (fun ITLIST' : type725 _25350 _25351 => @lem1101952 _25350 _25351 _17988 ITLIST')). Qed.
Lemma lem1101954 {_25350 _25351 : Type'} : (@ex ((_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350)) = (@ex ((_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350)).
Proof. exact (eq_refl (@ex ((_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350))). Qed.
Lemma lem1101955 {_25350 _25351 : Type'} (_17988 : type1671) : (term144 _25350 _25351 _17988) = (term127 _25350 _25351).
Proof. exact (MK_COMB (@lem1101954 _25350 _25351) (@lem1101953 _25350 _25351 _17988)). Qed.
Lemma lem1101956 {_25350 _25351 : Type'} : (term145 _25350 _25351) = (term146 _25350 _25351).
Proof. exact (fun_ext (fun _17988 : type1671 => @lem1101955 _25350 _25351 _17988)). Qed.
Lemma lem1101957 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1101958 {_25350 _25351 : Type'} : (term137 _25350 _25351) = (term131 _25350 _25351).
Proof. exact (MK_COMB (@lem1101957) (@lem1101956 _25350 _25351)). Qed.
Lemma lem1101959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1101960 {_25350 _25351 : Type'} : (term147 _25350 _25351) = (term148 _25350 _25351).
Proof. exact (MK_COMB (@lem1101959) (@lem1101958 _25350 _25351)). Qed.
Lemma lem1101961 {_25350 _25351 : Type'} (_17988 : type1671) : (term140 _25350 _25351 _17988) = (term128 _25350 _25351).
Proof. exact (eq_refl (term140 _25350 _25351 _17988)). Qed.
Lemma lem1101962 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) (_17988 : type1671) : (ITLIST' _17988) = (ITLIST' _17988).
Proof. exact (eq_refl (ITLIST' _17988)). Qed.
Lemma lem1101963 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) (_17988 : type1671) : (term149 _25350 _25351 ITLIST' _17988) = (term150 _25350 _25351 ITLIST' _17988).
Proof. exact (MK_COMB (@lem1101961 _25350 _25351 _17988) (@lem1101962 _25350 _25351 ITLIST' _17988)). Qed.
Lemma lem1101964 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) (_17988 : type1671) : (term150 _25350 _25351 ITLIST' _17988) = (term151 _25350 _25351 ITLIST' _17988).
Proof. exact (eq_refl (term150 _25350 _25351 ITLIST' _17988)). Qed.
Lemma lem1101965 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) (_17988 : type1671) : (term149 _25350 _25351 ITLIST' _17988) = (term151 _25350 _25351 ITLIST' _17988).
Proof. exact (TRANS (@lem1101963 _25350 _25351 ITLIST' _17988) (@lem1101964 _25350 _25351 ITLIST' _17988)). Qed.
Lemma lem1101966 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) : (term152 _25350 _25351 ITLIST') = (term153 _25350 _25351 ITLIST').
Proof. exact (fun_ext (fun _17988 : type1671 => @lem1101965 _25350 _25351 ITLIST' _17988)). Qed.
Lemma lem1101967 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1101968 {_25350 _25351 : Type'} (ITLIST' : type1268 _25350 _25351) : (term154 _25350 _25351 ITLIST') = (term155 _25350 _25351 ITLIST').
Proof. exact (MK_COMB (@lem1101967) (@lem1101966 _25350 _25351 ITLIST')). Qed.
Lemma lem1101969 {_25350 _25351 : Type'} : (term156 _25350 _25351) = (term157 _25350 _25351).
Proof. exact (fun_ext (fun ITLIST' : type1268 _25350 _25351 => @lem1101968 _25350 _25351 ITLIST')). Qed.
Lemma lem1101970 {_25350 _25351 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350))). Qed.
Lemma lem1101971 {_25350 _25351 : Type'} : (term138 _25350 _25351) = (term158 _25350 _25351).
Proof. exact (MK_COMB (@lem1101970 _25350 _25351) (@lem1101969 _25350 _25351)). Qed.
Lemma lem1101972 {_25350 _25351 : Type'} : ((term137 _25350 _25351) = (term138 _25350 _25351)) = ((term131 _25350 _25351) = (term158 _25350 _25351)).
Proof. exact (MK_COMB (@lem1101960 _25350 _25351) (@lem1101971 _25350 _25351)). Qed.
Lemma lem1101973 {_25350 _25351 : Type'} : (term131 _25350 _25351) = (term158 _25350 _25351).
Proof. exact (EQ_MP (@lem1101972 _25350 _25351) (@lem1101947 _25350 _25351)). Qed.
Lemma lem1101974 {_25350 _25351 : Type'} : term158 _25350 _25351.
Proof. exact (EQ_MP (@lem1101973 _25350 _25351) (@lem1101940 _25350 _25351)). Qed.
Lemma lem1101976 {A : Type'} : (@ex A) = (term159 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1101977 {_25350 _25351 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350)) = (term160 _25350 _25351).
Proof. exact (@lem1101976 (type1268 _25350 _25351)). Qed.
Lemma lem1101978 {_25350 _25351 : Type'} : (term157 _25350 _25351) = (term157 _25350 _25351).
Proof. exact (eq_refl (term157 _25350 _25351)). Qed.
Lemma lem1101979 {_25350 _25351 : Type'} : (term158 _25350 _25351) = (term161 _25350 _25351).
Proof. exact (MK_COMB (@lem1101977 _25350 _25351) (@lem1101978 _25350 _25351)). Qed.
Lemma lem1101980 {_25350 _25351 : Type'} : (term161 _25350 _25351) = (term162 _25350 _25351).
Proof. exact (eq_refl (term161 _25350 _25351)). Qed.
Lemma lem1101981 {_25350 _25351 : Type'} : (term158 _25350 _25351) = (term162 _25350 _25351).
Proof. exact (TRANS (@lem1101979 _25350 _25351) (@lem1101980 _25350 _25351)). Qed.
Lemma lem1101982 {_25350 _25351 : Type'} : term162 _25350 _25351.
Proof. exact (EQ_MP (@lem1101981 _25350 _25351) (@lem1101974 _25350 _25351)). Qed.
