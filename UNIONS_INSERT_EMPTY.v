Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_INSERT_EMPTY_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_INSERT_spec.
Require Import IN_UNIONS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3350707 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3350708 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3350709 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3350708 A x) (@lem3350707 A x)). Qed.
Lemma lem3350710 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3350709 A x y). Qed.
Lemma lem3350711 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3350712 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem3350711 A y x) (@lem3350710 A x y)). Qed.
Lemma lem3350713 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem3350712 A y x s). Qed.
Lemma lem3350714 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem3350716 {A : Type'} (s : type686 A) : term7 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3350717 {A : Type'} (s : type686 A) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3350718 {A : Type'} (s : type686 A) : term8 A s.
Proof. exact (EQ_MP (@lem3350717 A s) (@lem3350716 A s)). Qed.
Lemma lem3350719 {A : Type'} (s : type686 A) (x : A) : term9 A s x.
Proof. exact (@lem3350718 A s x). Qed.
Lemma lem3350720 {A : Type'} (s : type686 A) (x : A) : (term9 A s x) = ((term10 A x s) = (term11 A s x)).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3350722 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3350723 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3350724 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem3350723 A s) (@lem3350722 A s)). Qed.
Lemma lem3350725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem3350724 A s t). Qed.
Lemma lem3350726 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem3350735 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem3350726 A s t) (@lem3350725 A s t)). Qed.
Lemma lem3350736 {_87210 : Type'} (s : _87210 -> Prop) (t : _87210 -> Prop) : (s = t) = (term15 _87210 s t).
Proof. exact (@lem3350735 _87210 s t). Qed.
Lemma lem3350737 {_87210 : Type'} (s : type686 _87210) : ((term16 _87210 s) = (@UNIONS _87210 s)) = (term17 _87210 s).
Proof. exact (@lem3350736 _87210 (term16 _87210 s) (@UNIONS _87210 s)). Qed.
Lemma lem3350738 {_87210 : Type'} : (term18 _87210) = (term19 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3350737 _87210 s)). Qed.
Lemma lem3350739 {_87210 : Type'} : (@all ((_87210 -> Prop) -> Prop)) = (@all ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3350740 {_87210 : Type'} : (term20 _87210) = (term21 _87210).
Proof. exact (MK_COMB (@lem3350739 _87210) (@lem3350738 _87210)). Qed.
Lemma lem3350741 {_87210 : Type'} : (term21 _87210) = (term20 _87210).
Proof. exact (SYM (@lem3350740 _87210)). Qed.
Lemma lem3350753 {A : Type'} (s : type686 A) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (EQ_MP (@lem3350720 A s x) (@lem3350719 A s x)). Qed.
Lemma lem3350754 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term10 _87210 x s) = (term11 _87210 s x).
Proof. exact (@lem3350753 _87210 s x). Qed.
Lemma lem3350755 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term22 _87210 x s) = (term23 _87210 s x).
Proof. exact (@lem3350754 _87210 (@INSERT (_87210 -> Prop) (@EMPTY _87210) s) x). Qed.
Lemma lem3350763 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3350714 A y x s) (@lem3350713 A y x s)). Qed.
Lemma lem3350764 {_87210 : Type'} (y : _87210 -> Prop) (x : _87210 -> Prop) (s : type686 _87210) : (term24 _87210 x y s) = (term25 _87210 y x s).
Proof. exact (@lem3350763 (_87210 -> Prop) y x s). Qed.
Lemma lem3350765 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term26 _87210 t s) = (term27 _87210 t s).
Proof. exact (@lem3350764 _87210 (@EMPTY _87210) t s). Qed.
Lemma lem3350770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3350771 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term28 _87210 t s) = (term29 _87210 t s).
Proof. exact (MK_COMB (@lem3350770) (@lem3350765 _87210 t s)). Qed.
Lemma lem3350772 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (@IN _87210 x t) = (@IN _87210 x t).
Proof. exact (eq_refl (@IN _87210 x t)). Qed.
Lemma lem3350773 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term30 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (MK_COMB (@lem3350771 _87210 t s) (@lem3350772 _87210 x t)). Qed.
Lemma lem3350776 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term32 _87210 s x) = (term33 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3350773 _87210 s x t)). Qed.
Lemma lem3350777 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3350778 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term23 _87210 s x) = (term34 _87210 s x).
Proof. exact (MK_COMB (@lem3350777 _87210) (@lem3350776 _87210 s x)). Qed.
Lemma lem3350783 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term22 _87210 x s) = (term34 _87210 s x).
Proof. exact (TRANS (@lem3350755 _87210 s x) (@lem3350778 _87210 s x)). Qed.
Lemma lem3350784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3350785 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term35 _87210 x s) = (term36 _87210 s x).
Proof. exact (MK_COMB (@lem3350784) (@lem3350783 _87210 s x)). Qed.
Lemma lem3350787 {A : Type'} (s : type686 A) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (EQ_MP (@lem3350720 A s x) (@lem3350719 A s x)). Qed.
Lemma lem3350788 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term10 _87210 x s) = (term11 _87210 s x).
Proof. exact (@lem3350787 _87210 s x). Qed.
Lemma lem3350795 {_87210 : Type'} (s : type686 _87210) (x : _87210) : ((term22 _87210 x s) = (term10 _87210 x s)) = ((term34 _87210 s x) = (term11 _87210 s x)).
Proof. exact (MK_COMB (@lem3350785 _87210 s x) (@lem3350788 _87210 s x)). Qed.
Lemma lem3350798 {_87210 : Type'} (s : type686 _87210) : (term37 _87210 s) = (term38 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3350795 _87210 s x)). Qed.
Lemma lem3350799 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3350800 {_87210 : Type'} (s : type686 _87210) : (term17 _87210 s) = (term39 _87210 s).
Proof. exact (MK_COMB (@lem3350799 _87210) (@lem3350798 _87210 s)). Qed.
Lemma lem3350805 {_87210 : Type'} : (term19 _87210) = (term40 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3350800 _87210 s)). Qed.
Lemma lem3350806 {_87210 : Type'} : (@all ((_87210 -> Prop) -> Prop)) = (@all ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3350807 {_87210 : Type'} : (term21 _87210) = (term41 _87210).
Proof. exact (MK_COMB (@lem3350806 _87210) (@lem3350805 _87210)). Qed.
Lemma lem3350812 {_87210 : Type'} : (term41 _87210) = (term21 _87210).
Proof. exact (SYM (@lem3350807 _87210)). Qed.
Lemma lem3350814 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3350815 {_87210 : Type'} : (term41 _87210) = (term43 _87210).
Proof. exact (@lem3350814 (term41 _87210)). Qed.
Lemma lem3350816 {_87210 : Type'} : (term43 _87210) = (term41 _87210).
Proof. exact (SYM (@lem3350815 _87210)). Qed.
Lemma lem3350817 {_87210 : Type'} (h1 : term44 _87210) : term44 _87210.
Proof. exact (h1). Qed.
Lemma lem3350818 {_87210 : Type'} : term45 _87210.
Proof. exact (@lem3204775 (_87210 -> Prop)). Qed.
Lemma lem3350819 {_87210 : Type'} : term46 _87210.
Proof. exact (@lem3204775 _87210). Qed.
Lemma lem3350823 {_87210 : Type'} (h1 : term47 _87210) : term47 _87210.
Proof. exact (h1). Qed.
Lemma lem3350824 {_87210 : Type'} : term48 _87210.
Proof. exact (fun h0 : term47 _87210 => @lem3350823 _87210 h0). Qed.
Lemma lem3350825 {_87210 : Type'} (h1 : term48 _87210) : term48 _87210.
Proof. exact (h1). Qed.
Lemma lem3350826 {_87210 : Type'} (h1 : term47 _87210) : term47 _87210.
Proof. exact (h1). Qed.
Lemma lem3350827 {_87210 : Type'} (h1 : term47 _87210) (h2 : term48 _87210) : term47 _87210.
Proof. exact (@lem3350825 _87210 h2 (@lem3350826 _87210 h1)). Qed.
Lemma lem3350828 {_87210 : Type'} (h1 : term47 _87210) : term49 _87210.
Proof. exact (fun h0 : term48 _87210 => @lem3350827 _87210 h1 h0). Qed.
Lemma lem3350829 {_87210 : Type'} (h1 : term48 _87210) : term48 _87210.
Proof. exact (h1). Qed.
Lemma lem3350830 {_87210 : Type'} (h1 : term47 _87210) (h2 : term48 _87210) : term47 _87210.
Proof. exact (@lem3350828 _87210 h1 (@lem3350829 _87210 h2)). Qed.
Lemma lem3350831 {_87210 : Type'} (h1 : term48 _87210) : term48 _87210.
Proof. exact (fun h0 : term47 _87210 => @lem3350830 _87210 h0 h1). Qed.
Lemma lem3350832 {_87210 : Type'} : term50 _87210.
Proof. exact (fun h0 : term48 _87210 => @lem3350831 _87210 h0). Qed.
Lemma lem3350835 {_87210 : Type'} : term48 _87210.
Proof. exact (@lem3350832 _87210 (@lem3350824 _87210)). Qed.
Lemma lem3350836 {_87210 : Type'} : term48 _87210.
Proof. exact (@lem3350835 _87210). Qed.
Lemma lem3350956 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3350957 {_87210 : Type'} : (term51 _87210) = (term52 _87210).
Proof. exact (@lem3350956 (term45 _87210)). Qed.
Lemma lem3350962 {_87210 : Type'} : (term53 _87210) = (term53 _87210).
Proof. exact (eq_refl (term53 _87210)). Qed.
Lemma lem3350963 {_87210 : Type'} : (term54 _87210) = (term55 _87210).
Proof. exact (MK_COMB (@lem3350962 _87210) (@lem3350957 _87210)). Qed.
Lemma lem3350966 {_87210 : Type'} : (term56 _87210) = (term56 _87210).
Proof. exact (eq_refl (term56 _87210)). Qed.
Lemma lem3350973 {_87210 : Type'} : (term47 _87210) = (term57 _87210).
Proof. exact (MK_COMB (@lem3350966 _87210) (@lem3350963 _87210)). Qed.
Lemma lem3350976 {_87210 : Type'} (x : _87210 -> Prop) : (term58 _87210 x) = (term58 _87210 x).
Proof. exact (eq_refl (term58 _87210 x)). Qed.
Lemma lem3350977 {_87210 : Type'} : (term59 _87210) = (term59 _87210).
Proof. exact (fun_ext (fun x : _87210 -> Prop => @lem3350976 _87210 x)). Qed.
Lemma lem3350978 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3350979 {_87210 : Type'} : (term45 _87210) = (term45 _87210).
Proof. exact (MK_COMB (@lem3350978 _87210) (@lem3350977 _87210)). Qed.
Lemma lem3350980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3350981 {_87210 : Type'} : (term52 _87210) = (term52 _87210).
Proof. exact (MK_COMB (@lem3350980) (@lem3350979 _87210)). Qed.
Lemma lem3350984 {_87210 : Type'} (x : _87210) : (term60 _87210 x) = (term60 _87210 x).
Proof. exact (eq_refl (term60 _87210 x)). Qed.
Lemma lem3350985 {_87210 : Type'} : (term61 _87210) = (term61 _87210).
Proof. exact (fun_ext (fun x : _87210 => @lem3350984 _87210 x)). Qed.
Lemma lem3350986 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3350987 {_87210 : Type'} : (term46 _87210) = (term46 _87210).
Proof. exact (MK_COMB (@lem3350986 _87210) (@lem3350985 _87210)). Qed.
Lemma lem3350988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3350989 {_87210 : Type'} : (term53 _87210) = (term53 _87210).
Proof. exact (MK_COMB (@lem3350988) (@lem3350987 _87210)). Qed.
Lemma lem3350990 {_87210 : Type'} : (term55 _87210) = (term55 _87210).
Proof. exact (MK_COMB (@lem3350989 _87210) (@lem3350981 _87210)). Qed.
Lemma lem3350995 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term62 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term62 _87210 s x t)). Qed.
Lemma lem3350996 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term63 _87210 s x) = (term63 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3350995 _87210 s x t)). Qed.
Lemma lem3350997 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3350998 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term11 _87210 s x) = (term11 _87210 s x).
Proof. exact (MK_COMB (@lem3350997 _87210) (@lem3350996 _87210 s x)). Qed.
Lemma lem3351007 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term31 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (eq_refl (term31 _87210 s x t)). Qed.
Lemma lem3351008 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term33 _87210 s x) = (term33 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351007 _87210 s x t)). Qed.
Lemma lem3351009 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351010 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term34 _87210 s x) = (term34 _87210 s x).
Proof. exact (MK_COMB (@lem3351009 _87210) (@lem3351008 _87210 s x)). Qed.
Lemma lem3351011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351012 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term36 _87210 s x) = (term36 _87210 s x).
Proof. exact (MK_COMB (@lem3351011) (@lem3351010 _87210 s x)). Qed.
Lemma lem3351013 {_87210 : Type'} (s : type686 _87210) (x : _87210) : ((term34 _87210 s x) = (term11 _87210 s x)) = ((term34 _87210 s x) = (term11 _87210 s x)).
Proof. exact (MK_COMB (@lem3351012 _87210 s x) (@lem3350998 _87210 s x)). Qed.
Lemma lem3351014 {_87210 : Type'} (s : type686 _87210) : (term38 _87210 s) = (term38 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351013 _87210 s x)). Qed.
Lemma lem3351015 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3351016 {_87210 : Type'} (s : type686 _87210) : (term39 _87210 s) = (term39 _87210 s).
Proof. exact (MK_COMB (@lem3351015 _87210) (@lem3351014 _87210 s)). Qed.
Lemma lem3351017 {_87210 : Type'} : (term40 _87210) = (term40 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351016 _87210 s)). Qed.
Lemma lem3351018 {_87210 : Type'} : (@all ((_87210 -> Prop) -> Prop)) = (@all ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351019 {_87210 : Type'} : (term41 _87210) = (term41 _87210).
Proof. exact (MK_COMB (@lem3351018 _87210) (@lem3351017 _87210)). Qed.
Lemma lem3351020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3351021 {_87210 : Type'} : (term44 _87210) = (term44 _87210).
Proof. exact (MK_COMB (@lem3351020) (@lem3351019 _87210)). Qed.
Lemma lem3351022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3351023 {_87210 : Type'} : (term56 _87210) = (term56 _87210).
Proof. exact (MK_COMB (@lem3351022) (@lem3351021 _87210)). Qed.
Lemma lem3351024 {_87210 : Type'} : (term57 _87210) = (term57 _87210).
Proof. exact (MK_COMB (@lem3351023 _87210) (@lem3350990 _87210)). Qed.
Lemma lem3351073 {_87210 : Type'} : (term47 _87210) = (term57 _87210).
Proof. exact (TRANS (@lem3350973 _87210) (@lem3351024 _87210)). Qed.
Lemma lem3351074 {_87210 : Type'} : (term57 _87210) = (term47 _87210).
Proof. exact (SYM (@lem3351073 _87210)). Qed.
Lemma lem3351075 {_87210 : Type'} (h1 : term44 _87210) : term44 _87210.
Proof. exact (h1). Qed.
Lemma lem3351076 {_87210 : Type'} (h1 : term46 _87210) : term46 _87210.
Proof. exact (h1). Qed.
Lemma lem3351086 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term64 _87210 t s) = (term65 _87210 t s).
Proof. exact (@lem17160 (t = (@EMPTY _87210)) (@IN (_87210 -> Prop) t s)). Qed.
Lemma lem3351090 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term66 _87210 x t) = (term66 _87210 x t).
Proof. exact (eq_refl (term66 _87210 x t)). Qed.
Lemma lem3351092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351093 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term67 _87210 t s) = (term68 _87210 t s).
Proof. exact (MK_COMB (@lem3351092) (@lem3351086 _87210 t s)). Qed.
Lemma lem3351094 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term69 _87210 s x t) = (term70 _87210 s x t).
Proof. exact (MK_COMB (@lem3351093 _87210 t s) (@lem3351090 _87210 x t)). Qed.
Lemma lem3351095 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term71 _87210 s x t) = (term69 _87210 s x t).
Proof. exact (@lem17045 (term27 _87210 t s) (@IN _87210 x t)). Qed.
Lemma lem3351096 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term71 _87210 s x t) = (term70 _87210 s x t).
Proof. exact (TRANS (@lem3351095 _87210 s x t) (@lem3351094 _87210 s x t)). Qed.
Lemma lem3351099 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term31 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (eq_refl (term31 _87210 s x t)). Qed.
Lemma lem3351100 {_87210 : Type'} (P : type686 _87210) : (term72 _87210 P) = (term73 _87210 P).
Proof. exact (@lem18394 (_87210 -> Prop) P). Qed.
Lemma lem3351101 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term74 _87210 s x) = (term75 _87210 s x).
Proof. exact (@lem3351100 _87210 (term33 _87210 s x)). Qed.
Lemma lem3351102 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term76 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (eq_refl (term76 _87210 s x t)). Qed.
Lemma lem3351103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3351104 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term77 _87210 s x t) = (term71 _87210 s x t).
Proof. exact (MK_COMB (@lem3351103) (@lem3351102 _87210 s x t)). Qed.
Lemma lem3351105 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term77 _87210 s x t) = (term70 _87210 s x t).
Proof. exact (TRANS (@lem3351104 _87210 s x t) (@lem3351096 _87210 s x t)). Qed.
Lemma lem3351106 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term78 _87210 s x) = (term79 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351105 _87210 s x t)). Qed.
Lemma lem3351107 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3351108 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term75 _87210 s x) = (term80 _87210 s x).
Proof. exact (MK_COMB (@lem3351107 _87210) (@lem3351106 _87210 s x)). Qed.
Lemma lem3351109 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term74 _87210 s x) = (term80 _87210 s x).
Proof. exact (TRANS (@lem3351101 _87210 s x) (@lem3351108 _87210 s x)). Qed.
Lemma lem3351110 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term33 _87210 s x) = (term33 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351099 _87210 s x t)). Qed.
Lemma lem3351111 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351112 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term34 _87210 s x) = (term34 _87210 s x).
Proof. exact (MK_COMB (@lem3351111 _87210) (@lem3351110 _87210 s x)). Qed.
Lemma lem3351121 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term81 _87210 s x t) = (term82 _87210 s x t).
Proof. exact (@lem17045 (@IN (_87210 -> Prop) t s) (@IN _87210 x t)). Qed.
Lemma lem3351124 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term62 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term62 _87210 s x t)). Qed.
Lemma lem3351125 {_87210 : Type'} (P : type686 _87210) : (term72 _87210 P) = (term73 _87210 P).
Proof. exact (@lem18394 (_87210 -> Prop) P). Qed.
Lemma lem3351126 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term83 _87210 s x) = (term84 _87210 s x).
Proof. exact (@lem3351125 _87210 (term63 _87210 s x)). Qed.
Lemma lem3351127 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term85 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term85 _87210 s x t)). Qed.
Lemma lem3351128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3351129 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term86 _87210 s x t) = (term81 _87210 s x t).
Proof. exact (MK_COMB (@lem3351128) (@lem3351127 _87210 s x t)). Qed.
Lemma lem3351130 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term86 _87210 s x t) = (term82 _87210 s x t).
Proof. exact (TRANS (@lem3351129 _87210 s x t) (@lem3351121 _87210 s x t)). Qed.
Lemma lem3351131 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term87 _87210 s x) = (term88 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351130 _87210 s x t)). Qed.
Lemma lem3351132 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3351133 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term84 _87210 s x) = (term89 _87210 s x).
Proof. exact (MK_COMB (@lem3351132 _87210) (@lem3351131 _87210 s x)). Qed.
Lemma lem3351134 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term83 _87210 s x) = (term89 _87210 s x).
Proof. exact (TRANS (@lem3351126 _87210 s x) (@lem3351133 _87210 s x)). Qed.
Lemma lem3351135 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term63 _87210 s x) = (term63 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351124 _87210 s x t)). Qed.
Lemma lem3351136 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351137 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term11 _87210 s x) = (term11 _87210 s x).
Proof. exact (MK_COMB (@lem3351136 _87210) (@lem3351135 _87210 s x)). Qed.
Lemma lem3351138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3351139 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term90 _87210 s x) = (term91 _87210 s x).
Proof. exact (MK_COMB (@lem3351138) (@lem3351109 _87210 s x)). Qed.
Lemma lem3351140 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term92 _87210 s x) = (term93 _87210 s x).
Proof. exact (MK_COMB (@lem3351139 _87210 s x) (@lem3351137 _87210 s x)). Qed.
Lemma lem3351141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3351142 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term94 _87210 s x) = (term94 _87210 s x).
Proof. exact (MK_COMB (@lem3351141) (@lem3351112 _87210 s x)). Qed.
Lemma lem3351143 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term95 _87210 s x) = (term96 _87210 s x).
Proof. exact (MK_COMB (@lem3351142 _87210 s x) (@lem3351134 _87210 s x)). Qed.
Lemma lem3351144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351145 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term97 _87210 s x) = (term98 _87210 s x).
Proof. exact (MK_COMB (@lem3351144) (@lem3351143 _87210 s x)). Qed.
Lemma lem3351146 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term99 _87210 s x) = (term100 _87210 s x).
Proof. exact (MK_COMB (@lem3351145 _87210 s x) (@lem3351140 _87210 s x)). Qed.
Lemma lem3351147 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term101 _87210 s x) = (term99 _87210 s x).
Proof. exact (@lem17646 (term34 _87210 s x) (term11 _87210 s x)). Qed.
Lemma lem3351148 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term101 _87210 s x) = (term100 _87210 s x).
Proof. exact (TRANS (@lem3351147 _87210 s x) (@lem3351146 _87210 s x)). Qed.
Lemma lem3351149 {_87210 : Type'} (P : _87210 -> Prop) : (term102 _87210 P) = (term103 _87210 P).
Proof. exact (@lem18392 _87210 P). Qed.
Lemma lem3351150 {_87210 : Type'} (s : type686 _87210) : (term104 _87210 s) = (term105 _87210 s).
Proof. exact (@lem3351149 _87210 (term38 _87210 s)). Qed.
Lemma lem3351151 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term106 _87210 s x) = ((term34 _87210 s x) = (term11 _87210 s x)).
Proof. exact (eq_refl (term106 _87210 s x)). Qed.
Lemma lem3351152 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3351153 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term107 _87210 s x) = (term101 _87210 s x).
Proof. exact (MK_COMB (@lem3351152) (@lem3351151 _87210 s x)). Qed.
Lemma lem3351154 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term107 _87210 s x) = (term100 _87210 s x).
Proof. exact (TRANS (@lem3351153 _87210 s x) (@lem3351148 _87210 s x)). Qed.
Lemma lem3351155 {_87210 : Type'} (s : type686 _87210) : (term108 _87210 s) = (term109 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351154 _87210 s x)). Qed.
Lemma lem3351156 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351157 {_87210 : Type'} (s : type686 _87210) : (term105 _87210 s) = (term110 _87210 s).
Proof. exact (MK_COMB (@lem3351156 _87210) (@lem3351155 _87210 s)). Qed.
Lemma lem3351158 {_87210 : Type'} (s : type686 _87210) : (term104 _87210 s) = (term110 _87210 s).
Proof. exact (TRANS (@lem3351150 _87210 s) (@lem3351157 _87210 s)). Qed.
Lemma lem3351159 {_87210 : Type'} (P : type180 _87210) : (term111 _87210 P) = (term112 _87210 P).
Proof. exact (@lem18392 (type686 _87210) P). Qed.
Lemma lem3351160 {_87210 : Type'} : (term44 _87210) = (term113 _87210).
Proof. exact (@lem3351159 _87210 (term40 _87210)). Qed.
Lemma lem3351161 {_87210 : Type'} (s : type686 _87210) : (term114 _87210 s) = (term39 _87210 s).
Proof. exact (eq_refl (term114 _87210 s)). Qed.
Lemma lem3351162 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3351163 {_87210 : Type'} (s : type686 _87210) : (term115 _87210 s) = (term104 _87210 s).
Proof. exact (MK_COMB (@lem3351162) (@lem3351161 _87210 s)). Qed.
Lemma lem3351164 {_87210 : Type'} (s : type686 _87210) : (term115 _87210 s) = (term110 _87210 s).
Proof. exact (TRANS (@lem3351163 _87210 s) (@lem3351158 _87210 s)). Qed.
Lemma lem3351165 {_87210 : Type'} : (term116 _87210) = (term117 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351164 _87210 s)). Qed.
Lemma lem3351166 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351167 {_87210 : Type'} : (term113 _87210) = (term118 _87210).
Proof. exact (MK_COMB (@lem3351166 _87210) (@lem3351165 _87210)). Qed.
Lemma lem3351168 {_87210 : Type'} : (term44 _87210) = (term118 _87210).
Proof. exact (TRANS (@lem3351160 _87210) (@lem3351167 _87210)). Qed.
Lemma lem3351174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3351175 {_87210 : Type'} (P : _87210 -> Prop) (Q : _87210 -> Prop) : (term119 _87210 P Q) = (term120 _87210 P Q).
Proof. exact (@lem3351174 _87210 P Q). Qed.
Lemma lem3351176 {_87210 : Type'} (s : type686 _87210) : (term121 _87210 s) = (term122 _87210 s).
Proof. exact (@lem3351175 _87210 (term123 _87210 s) (term124 _87210 s)). Qed.
Lemma lem3351177 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term125 _87210 s x) = (term96 _87210 s x).
Proof. exact (eq_refl (term125 _87210 s x)). Qed.
Lemma lem3351178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351179 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term126 _87210 s x) = (term98 _87210 s x).
Proof. exact (MK_COMB (@lem3351178) (@lem3351177 _87210 s x)). Qed.
Lemma lem3351180 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term127 _87210 s x) = (term93 _87210 s x).
Proof. exact (eq_refl (term127 _87210 s x)). Qed.
Lemma lem3351181 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term128 _87210 s x) = (term100 _87210 s x).
Proof. exact (MK_COMB (@lem3351179 _87210 s x) (@lem3351180 _87210 s x)). Qed.
Lemma lem3351182 {_87210 : Type'} (s : type686 _87210) : (term129 _87210 s) = (term109 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351181 _87210 s x)). Qed.
Lemma lem3351183 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351184 {_87210 : Type'} (s : type686 _87210) : (term121 _87210 s) = (term110 _87210 s).
Proof. exact (MK_COMB (@lem3351183 _87210) (@lem3351182 _87210 s)). Qed.
Lemma lem3351185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351186 {_87210 : Type'} (s : type686 _87210) : (term130 _87210 s) = (term131 _87210 s).
Proof. exact (MK_COMB (@lem3351185) (@lem3351184 _87210 s)). Qed.
Lemma lem3351187 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term125 _87210 s x) = (term96 _87210 s x).
Proof. exact (eq_refl (term125 _87210 s x)). Qed.
Lemma lem3351188 {_87210 : Type'} (s : type686 _87210) : (term132 _87210 s) = (term123 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351187 _87210 s x)). Qed.
Lemma lem3351189 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351190 {_87210 : Type'} (s : type686 _87210) : (term133 _87210 s) = (term134 _87210 s).
Proof. exact (MK_COMB (@lem3351189 _87210) (@lem3351188 _87210 s)). Qed.
Lemma lem3351191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351192 {_87210 : Type'} (s : type686 _87210) : (term135 _87210 s) = (term136 _87210 s).
Proof. exact (MK_COMB (@lem3351191) (@lem3351190 _87210 s)). Qed.
Lemma lem3351193 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term127 _87210 s x) = (term93 _87210 s x).
Proof. exact (eq_refl (term127 _87210 s x)). Qed.
Lemma lem3351194 {_87210 : Type'} (s : type686 _87210) : (term137 _87210 s) = (term124 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351193 _87210 s x)). Qed.
Lemma lem3351195 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351196 {_87210 : Type'} (s : type686 _87210) : (term138 _87210 s) = (term139 _87210 s).
Proof. exact (MK_COMB (@lem3351195 _87210) (@lem3351194 _87210 s)). Qed.
Lemma lem3351197 {_87210 : Type'} (s : type686 _87210) : (term122 _87210 s) = (term140 _87210 s).
Proof. exact (MK_COMB (@lem3351192 _87210 s) (@lem3351196 _87210 s)). Qed.
Lemma lem3351198 {_87210 : Type'} (s : type686 _87210) : ((term121 _87210 s) = (term122 _87210 s)) = ((term110 _87210 s) = (term140 _87210 s)).
Proof. exact (MK_COMB (@lem3351186 _87210 s) (@lem3351197 _87210 s)). Qed.
Lemma lem3351199 {_87210 : Type'} (s : type686 _87210) : (term110 _87210 s) = (term140 _87210 s).
Proof. exact (EQ_MP (@lem3351198 _87210 s) (@lem3351176 _87210 s)). Qed.
Lemma lem3351488 {_87210 : Type'} : (term117 _87210) = (term141 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351199 _87210 s)). Qed.
Lemma lem3351489 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351490 {_87210 : Type'} : (term118 _87210) = (term142 _87210).
Proof. exact (MK_COMB (@lem3351489 _87210) (@lem3351488 _87210)). Qed.
Lemma lem3351492 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3351493 {_87210 : Type'} (P : type180 _87210) (Q : type180 _87210) : (term143 _87210 P Q) = (term144 _87210 P Q).
Proof. exact (@lem3351492 (type686 _87210) P Q). Qed.
Lemma lem3351494 {_87210 : Type'} : (term145 _87210) = (term146 _87210).
Proof. exact (@lem3351493 _87210 (term147 _87210) (term148 _87210)). Qed.
Lemma lem3351495 {_87210 : Type'} (s : type686 _87210) : (term149 _87210 s) = (term134 _87210 s).
Proof. exact (eq_refl (term149 _87210 s)). Qed.
Lemma lem3351496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351497 {_87210 : Type'} (s : type686 _87210) : (term150 _87210 s) = (term136 _87210 s).
Proof. exact (MK_COMB (@lem3351496) (@lem3351495 _87210 s)). Qed.
Lemma lem3351498 {_87210 : Type'} (s : type686 _87210) : (term151 _87210 s) = (term139 _87210 s).
Proof. exact (eq_refl (term151 _87210 s)). Qed.
Lemma lem3351499 {_87210 : Type'} (s : type686 _87210) : (term152 _87210 s) = (term140 _87210 s).
Proof. exact (MK_COMB (@lem3351497 _87210 s) (@lem3351498 _87210 s)). Qed.
Lemma lem3351500 {_87210 : Type'} : (term153 _87210) = (term141 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351499 _87210 s)). Qed.
Lemma lem3351501 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351502 {_87210 : Type'} : (term145 _87210) = (term142 _87210).
Proof. exact (MK_COMB (@lem3351501 _87210) (@lem3351500 _87210)). Qed.
Lemma lem3351503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351504 {_87210 : Type'} : (term154 _87210) = (term155 _87210).
Proof. exact (MK_COMB (@lem3351503) (@lem3351502 _87210)). Qed.
Lemma lem3351505 {_87210 : Type'} (s : type686 _87210) : (term149 _87210 s) = (term134 _87210 s).
Proof. exact (eq_refl (term149 _87210 s)). Qed.
Lemma lem3351506 {_87210 : Type'} : (term156 _87210) = (term147 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351505 _87210 s)). Qed.
Lemma lem3351507 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351508 {_87210 : Type'} : (term157 _87210) = (term158 _87210).
Proof. exact (MK_COMB (@lem3351507 _87210) (@lem3351506 _87210)). Qed.
Lemma lem3351509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351510 {_87210 : Type'} : (term159 _87210) = (term160 _87210).
Proof. exact (MK_COMB (@lem3351509) (@lem3351508 _87210)). Qed.
Lemma lem3351511 {_87210 : Type'} (s : type686 _87210) : (term151 _87210 s) = (term139 _87210 s).
Proof. exact (eq_refl (term151 _87210 s)). Qed.
Lemma lem3351512 {_87210 : Type'} : (term161 _87210) = (term148 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351511 _87210 s)). Qed.
Lemma lem3351513 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351514 {_87210 : Type'} : (term162 _87210) = (term163 _87210).
Proof. exact (MK_COMB (@lem3351513 _87210) (@lem3351512 _87210)). Qed.
Lemma lem3351515 {_87210 : Type'} : (term146 _87210) = (term164 _87210).
Proof. exact (MK_COMB (@lem3351510 _87210) (@lem3351514 _87210)). Qed.
Lemma lem3351516 {_87210 : Type'} : ((term145 _87210) = (term146 _87210)) = ((term142 _87210) = (term164 _87210)).
Proof. exact (MK_COMB (@lem3351504 _87210) (@lem3351515 _87210)). Qed.
Lemma lem3351517 {_87210 : Type'} : (term142 _87210) = (term164 _87210).
Proof. exact (EQ_MP (@lem3351516 _87210) (@lem3351494 _87210)). Qed.
Lemma lem3351814 {_87210 : Type'} : (term118 _87210) = (term164 _87210).
Proof. exact (TRANS (@lem3351490 _87210) (@lem3351517 _87210)). Qed.
Lemma lem3351816 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3351817 {_87210 : Type'} (P : type686 _87210) (Q : Prop) : (term167 _87210 P Q) = (term168 _87210 P Q).
Proof. exact (@lem3351816 (_87210 -> Prop) P Q). Qed.
Lemma lem3351818 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term169 _87210 s x) = (term170 _87210 s x).
Proof. exact (@lem3351817 _87210 (term33 _87210 s x) (term89 _87210 s x)). Qed.
Lemma lem3351819 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term76 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (eq_refl (term76 _87210 s x t)). Qed.
Lemma lem3351820 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term171 _87210 s x) = (term33 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351819 _87210 s x t)). Qed.
Lemma lem3351821 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351822 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term172 _87210 s x) = (term34 _87210 s x).
Proof. exact (MK_COMB (@lem3351821 _87210) (@lem3351820 _87210 s x)). Qed.
Lemma lem3351823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3351824 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term173 _87210 s x) = (term94 _87210 s x).
Proof. exact (MK_COMB (@lem3351823) (@lem3351822 _87210 s x)). Qed.
Lemma lem3351825 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term89 _87210 s x) = (term89 _87210 s x).
Proof. exact (eq_refl (term89 _87210 s x)). Qed.
Lemma lem3351826 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term169 _87210 s x) = (term96 _87210 s x).
Proof. exact (MK_COMB (@lem3351824 _87210 s x) (@lem3351825 _87210 s x)). Qed.
Lemma lem3351827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351828 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term174 _87210 s x) = (term175 _87210 s x).
Proof. exact (MK_COMB (@lem3351827) (@lem3351826 _87210 s x)). Qed.
Lemma lem3351829 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term76 _87210 s x t) = (term31 _87210 s x t).
Proof. exact (eq_refl (term76 _87210 s x t)). Qed.
Lemma lem3351830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3351831 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term176 _87210 s x t) = (term177 _87210 s x t).
Proof. exact (MK_COMB (@lem3351830) (@lem3351829 _87210 s x t)). Qed.
Lemma lem3351832 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term89 _87210 s x) = (term89 _87210 s x).
Proof. exact (eq_refl (term89 _87210 s x)). Qed.
Lemma lem3351833 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term178 _87210 t s x) = (term179 _87210 t s x).
Proof. exact (MK_COMB (@lem3351831 _87210 s x t) (@lem3351832 _87210 s x)). Qed.
Lemma lem3351834 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term180 _87210 s x) = (term181 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351833 _87210 t s x)). Qed.
Lemma lem3351835 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351836 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term170 _87210 s x) = (term182 _87210 s x).
Proof. exact (MK_COMB (@lem3351835 _87210) (@lem3351834 _87210 s x)). Qed.
Lemma lem3351837 {_87210 : Type'} (s : type686 _87210) (x : _87210) : ((term169 _87210 s x) = (term170 _87210 s x)) = ((term96 _87210 s x) = (term182 _87210 s x)).
Proof. exact (MK_COMB (@lem3351828 _87210 s x) (@lem3351836 _87210 s x)). Qed.
Lemma lem3351838 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term96 _87210 s x) = (term182 _87210 s x).
Proof. exact (EQ_MP (@lem3351837 _87210 s x) (@lem3351818 _87210 s x)). Qed.
Lemma lem3351839 {_87210 : Type'} (s : type686 _87210) : (term123 _87210 s) = (term183 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351838 _87210 s x)). Qed.
Lemma lem3351840 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351841 {_87210 : Type'} (s : type686 _87210) : (term134 _87210 s) = (term184 _87210 s).
Proof. exact (MK_COMB (@lem3351840 _87210) (@lem3351839 _87210 s)). Qed.
Lemma lem3351842 {_87210 : Type'} : (term147 _87210) = (term185 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351841 _87210 s)). Qed.
Lemma lem3351843 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351844 {_87210 : Type'} : (term158 _87210) = (term186 _87210).
Proof. exact (MK_COMB (@lem3351843 _87210) (@lem3351842 _87210)). Qed.
Lemma lem3351845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351846 {_87210 : Type'} : (term160 _87210) = (term187 _87210).
Proof. exact (MK_COMB (@lem3351845) (@lem3351844 _87210)). Qed.
Lemma lem3351848 {A : Type'} (P : Prop) (Q : A -> Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3351849 {_87210 : Type'} (P : Prop) (Q : type686 _87210) : (term190 _87210 P Q) = (term191 _87210 P Q).
Proof. exact (@lem3351848 (_87210 -> Prop) P Q). Qed.
Lemma lem3351850 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term192 _87210 s x) = (term193 _87210 s x).
Proof. exact (@lem3351849 _87210 (term80 _87210 s x) (term63 _87210 s x)). Qed.
Lemma lem3351851 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term85 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term85 _87210 s x t)). Qed.
Lemma lem3351852 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term194 _87210 s x) = (term63 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351851 _87210 s x t)). Qed.
Lemma lem3351853 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351854 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term195 _87210 s x) = (term11 _87210 s x).
Proof. exact (MK_COMB (@lem3351853 _87210) (@lem3351852 _87210 s x)). Qed.
Lemma lem3351855 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term91 _87210 s x) = (term91 _87210 s x).
Proof. exact (eq_refl (term91 _87210 s x)). Qed.
Lemma lem3351856 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term192 _87210 s x) = (term93 _87210 s x).
Proof. exact (MK_COMB (@lem3351855 _87210 s x) (@lem3351854 _87210 s x)). Qed.
Lemma lem3351857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351858 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term196 _87210 s x) = (term197 _87210 s x).
Proof. exact (MK_COMB (@lem3351857) (@lem3351856 _87210 s x)). Qed.
Lemma lem3351859 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term85 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term85 _87210 s x t)). Qed.
Lemma lem3351860 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term91 _87210 s x) = (term91 _87210 s x).
Proof. exact (eq_refl (term91 _87210 s x)). Qed.
Lemma lem3351861 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term198 _87210 s x t) = (term199 _87210 s x t).
Proof. exact (MK_COMB (@lem3351860 _87210 s x) (@lem3351859 _87210 s x t)). Qed.
Lemma lem3351862 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term200 _87210 s x) = (term201 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351861 _87210 s x t)). Qed.
Lemma lem3351863 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351864 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term193 _87210 s x) = (term202 _87210 s x).
Proof. exact (MK_COMB (@lem3351863 _87210) (@lem3351862 _87210 s x)). Qed.
Lemma lem3351865 {_87210 : Type'} (s : type686 _87210) (x : _87210) : ((term192 _87210 s x) = (term193 _87210 s x)) = ((term93 _87210 s x) = (term202 _87210 s x)).
Proof. exact (MK_COMB (@lem3351858 _87210 s x) (@lem3351864 _87210 s x)). Qed.
Lemma lem3351866 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term93 _87210 s x) = (term202 _87210 s x).
Proof. exact (EQ_MP (@lem3351865 _87210 s x) (@lem3351850 _87210 s x)). Qed.
Lemma lem3351867 {_87210 : Type'} (s : type686 _87210) : (term124 _87210 s) = (term203 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351866 _87210 s x)). Qed.
Lemma lem3351868 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351869 {_87210 : Type'} (s : type686 _87210) : (term139 _87210 s) = (term204 _87210 s).
Proof. exact (MK_COMB (@lem3351868 _87210) (@lem3351867 _87210 s)). Qed.
Lemma lem3351870 {_87210 : Type'} : (term148 _87210) = (term205 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351869 _87210 s)). Qed.
Lemma lem3351871 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351872 {_87210 : Type'} : (term163 _87210) = (term206 _87210).
Proof. exact (MK_COMB (@lem3351871 _87210) (@lem3351870 _87210)). Qed.
Lemma lem3351873 {_87210 : Type'} : (term164 _87210) = (term207 _87210).
Proof. exact (MK_COMB (@lem3351846 _87210) (@lem3351872 _87210)). Qed.
Lemma lem3351875 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3351876 {_87210 : Type'} (P : type180 _87210) (Q : type180 _87210) : (term144 _87210 P Q) = (term143 _87210 P Q).
Proof. exact (@lem3351875 (type686 _87210) P Q). Qed.
Lemma lem3351877 {_87210 : Type'} : (term208 _87210) = (term209 _87210).
Proof. exact (@lem3351876 _87210 (term185 _87210) (term205 _87210)). Qed.
Lemma lem3351878 {_87210 : Type'} (s : type686 _87210) : (term210 _87210 s) = (term184 _87210 s).
Proof. exact (eq_refl (term210 _87210 s)). Qed.
Lemma lem3351879 {_87210 : Type'} : (term211 _87210) = (term185 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351878 _87210 s)). Qed.
Lemma lem3351880 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351881 {_87210 : Type'} : (term212 _87210) = (term186 _87210).
Proof. exact (MK_COMB (@lem3351880 _87210) (@lem3351879 _87210)). Qed.
Lemma lem3351882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351883 {_87210 : Type'} : (term213 _87210) = (term187 _87210).
Proof. exact (MK_COMB (@lem3351882) (@lem3351881 _87210)). Qed.
Lemma lem3351884 {_87210 : Type'} (s : type686 _87210) : (term214 _87210 s) = (term204 _87210 s).
Proof. exact (eq_refl (term214 _87210 s)). Qed.
Lemma lem3351885 {_87210 : Type'} : (term215 _87210) = (term205 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351884 _87210 s)). Qed.
Lemma lem3351886 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351887 {_87210 : Type'} : (term216 _87210) = (term206 _87210).
Proof. exact (MK_COMB (@lem3351886 _87210) (@lem3351885 _87210)). Qed.
Lemma lem3351888 {_87210 : Type'} : (term208 _87210) = (term207 _87210).
Proof. exact (MK_COMB (@lem3351883 _87210) (@lem3351887 _87210)). Qed.
Lemma lem3351889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351890 {_87210 : Type'} : (term217 _87210) = (term218 _87210).
Proof. exact (MK_COMB (@lem3351889) (@lem3351888 _87210)). Qed.
Lemma lem3351891 {_87210 : Type'} (s : type686 _87210) : (term210 _87210 s) = (term184 _87210 s).
Proof. exact (eq_refl (term210 _87210 s)). Qed.
Lemma lem3351892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351893 {_87210 : Type'} (s : type686 _87210) : (term219 _87210 s) = (term220 _87210 s).
Proof. exact (MK_COMB (@lem3351892) (@lem3351891 _87210 s)). Qed.
Lemma lem3351894 {_87210 : Type'} (s : type686 _87210) : (term214 _87210 s) = (term204 _87210 s).
Proof. exact (eq_refl (term214 _87210 s)). Qed.
Lemma lem3351895 {_87210 : Type'} (s : type686 _87210) : (term221 _87210 s) = (term222 _87210 s).
Proof. exact (MK_COMB (@lem3351893 _87210 s) (@lem3351894 _87210 s)). Qed.
Lemma lem3351896 {_87210 : Type'} : (term223 _87210) = (term224 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351895 _87210 s)). Qed.
Lemma lem3351897 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351898 {_87210 : Type'} : (term209 _87210) = (term225 _87210).
Proof. exact (MK_COMB (@lem3351897 _87210) (@lem3351896 _87210)). Qed.
Lemma lem3351899 {_87210 : Type'} : ((term208 _87210) = (term209 _87210)) = ((term207 _87210) = (term225 _87210)).
Proof. exact (MK_COMB (@lem3351890 _87210) (@lem3351898 _87210)). Qed.
Lemma lem3351900 {_87210 : Type'} : (term207 _87210) = (term225 _87210).
Proof. exact (EQ_MP (@lem3351899 _87210) (@lem3351877 _87210)). Qed.
Lemma lem3351902 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3351903 {_87210 : Type'} (P : _87210 -> Prop) (Q : _87210 -> Prop) : (term120 _87210 P Q) = (term119 _87210 P Q).
Proof. exact (@lem3351902 _87210 P Q). Qed.
Lemma lem3351904 {_87210 : Type'} (s : type686 _87210) : (term226 _87210 s) = (term227 _87210 s).
Proof. exact (@lem3351903 _87210 (term183 _87210 s) (term203 _87210 s)). Qed.
Lemma lem3351905 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term228 _87210 s x) = (term182 _87210 s x).
Proof. exact (eq_refl (term228 _87210 s x)). Qed.
Lemma lem3351906 {_87210 : Type'} (s : type686 _87210) : (term229 _87210 s) = (term183 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351905 _87210 s x)). Qed.
Lemma lem3351907 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351908 {_87210 : Type'} (s : type686 _87210) : (term230 _87210 s) = (term184 _87210 s).
Proof. exact (MK_COMB (@lem3351907 _87210) (@lem3351906 _87210 s)). Qed.
Lemma lem3351909 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351910 {_87210 : Type'} (s : type686 _87210) : (term231 _87210 s) = (term220 _87210 s).
Proof. exact (MK_COMB (@lem3351909) (@lem3351908 _87210 s)). Qed.
Lemma lem3351911 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term232 _87210 s x) = (term202 _87210 s x).
Proof. exact (eq_refl (term232 _87210 s x)). Qed.
Lemma lem3351912 {_87210 : Type'} (s : type686 _87210) : (term233 _87210 s) = (term203 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351911 _87210 s x)). Qed.
Lemma lem3351913 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351914 {_87210 : Type'} (s : type686 _87210) : (term234 _87210 s) = (term204 _87210 s).
Proof. exact (MK_COMB (@lem3351913 _87210) (@lem3351912 _87210 s)). Qed.
Lemma lem3351915 {_87210 : Type'} (s : type686 _87210) : (term226 _87210 s) = (term222 _87210 s).
Proof. exact (MK_COMB (@lem3351910 _87210 s) (@lem3351914 _87210 s)). Qed.
Lemma lem3351916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351917 {_87210 : Type'} (s : type686 _87210) : (term235 _87210 s) = (term236 _87210 s).
Proof. exact (MK_COMB (@lem3351916) (@lem3351915 _87210 s)). Qed.
Lemma lem3351918 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term228 _87210 s x) = (term182 _87210 s x).
Proof. exact (eq_refl (term228 _87210 s x)). Qed.
Lemma lem3351919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351920 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term237 _87210 s x) = (term238 _87210 s x).
Proof. exact (MK_COMB (@lem3351919) (@lem3351918 _87210 s x)). Qed.
Lemma lem3351921 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term232 _87210 s x) = (term202 _87210 s x).
Proof. exact (eq_refl (term232 _87210 s x)). Qed.
Lemma lem3351922 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term239 _87210 s x) = (term240 _87210 s x).
Proof. exact (MK_COMB (@lem3351920 _87210 s x) (@lem3351921 _87210 s x)). Qed.
Lemma lem3351923 {_87210 : Type'} (s : type686 _87210) : (term241 _87210 s) = (term242 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351922 _87210 s x)). Qed.
Lemma lem3351924 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351925 {_87210 : Type'} (s : type686 _87210) : (term227 _87210 s) = (term243 _87210 s).
Proof. exact (MK_COMB (@lem3351924 _87210) (@lem3351923 _87210 s)). Qed.
Lemma lem3351926 {_87210 : Type'} (s : type686 _87210) : ((term226 _87210 s) = (term227 _87210 s)) = ((term222 _87210 s) = (term243 _87210 s)).
Proof. exact (MK_COMB (@lem3351917 _87210 s) (@lem3351925 _87210 s)). Qed.
Lemma lem3351927 {_87210 : Type'} (s : type686 _87210) : (term222 _87210 s) = (term243 _87210 s).
Proof. exact (EQ_MP (@lem3351926 _87210 s) (@lem3351904 _87210 s)). Qed.
Lemma lem3351929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3351930 {_87210 : Type'} (P : type686 _87210) (Q : type686 _87210) : (term244 _87210 P Q) = (term245 _87210 P Q).
Proof. exact (@lem3351929 (_87210 -> Prop) P Q). Qed.
Lemma lem3351931 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term246 _87210 s x) = (term247 _87210 s x).
Proof. exact (@lem3351930 _87210 (term181 _87210 s x) (term201 _87210 s x)). Qed.
Lemma lem3351932 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term248 _87210 s x t) = (term179 _87210 t s x).
Proof. exact (eq_refl (term248 _87210 s x t)). Qed.
Lemma lem3351933 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term249 _87210 s x) = (term181 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351932 _87210 t s x)). Qed.
Lemma lem3351934 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351935 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term250 _87210 s x) = (term182 _87210 s x).
Proof. exact (MK_COMB (@lem3351934 _87210) (@lem3351933 _87210 s x)). Qed.
Lemma lem3351936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351937 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term251 _87210 s x) = (term238 _87210 s x).
Proof. exact (MK_COMB (@lem3351936) (@lem3351935 _87210 s x)). Qed.
Lemma lem3351938 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term252 _87210 s x t) = (term199 _87210 s x t).
Proof. exact (eq_refl (term252 _87210 s x t)). Qed.
Lemma lem3351939 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term253 _87210 s x) = (term201 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351938 _87210 s x t)). Qed.
Lemma lem3351940 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351941 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term254 _87210 s x) = (term202 _87210 s x).
Proof. exact (MK_COMB (@lem3351940 _87210) (@lem3351939 _87210 s x)). Qed.
Lemma lem3351942 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term246 _87210 s x) = (term240 _87210 s x).
Proof. exact (MK_COMB (@lem3351937 _87210 s x) (@lem3351941 _87210 s x)). Qed.
Lemma lem3351943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3351944 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term255 _87210 s x) = (term256 _87210 s x).
Proof. exact (MK_COMB (@lem3351943) (@lem3351942 _87210 s x)). Qed.
Lemma lem3351945 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term248 _87210 s x t) = (term179 _87210 t s x).
Proof. exact (eq_refl (term248 _87210 s x t)). Qed.
Lemma lem3351946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3351947 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term257 _87210 s x t) = (term258 _87210 t s x).
Proof. exact (MK_COMB (@lem3351946) (@lem3351945 _87210 t s x)). Qed.
Lemma lem3351948 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term252 _87210 s x t) = (term199 _87210 s x t).
Proof. exact (eq_refl (term252 _87210 s x t)). Qed.
Lemma lem3351949 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term259 _87210 s x t) = (term260 _87210 s x t).
Proof. exact (MK_COMB (@lem3351947 _87210 t s x) (@lem3351948 _87210 s x t)). Qed.
Lemma lem3351950 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term261 _87210 s x) = (term262 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3351949 _87210 s x t)). Qed.
Lemma lem3351951 {_87210 : Type'} : (@ex (_87210 -> Prop)) = (@ex (_87210 -> Prop)).
Proof. exact (eq_refl (@ex (_87210 -> Prop))). Qed.
Lemma lem3351952 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term247 _87210 s x) = (term263 _87210 s x).
Proof. exact (MK_COMB (@lem3351951 _87210) (@lem3351950 _87210 s x)). Qed.
Lemma lem3351953 {_87210 : Type'} (s : type686 _87210) (x : _87210) : ((term246 _87210 s x) = (term247 _87210 s x)) = ((term240 _87210 s x) = (term263 _87210 s x)).
Proof. exact (MK_COMB (@lem3351944 _87210 s x) (@lem3351952 _87210 s x)). Qed.
Lemma lem3351954 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term240 _87210 s x) = (term263 _87210 s x).
Proof. exact (EQ_MP (@lem3351953 _87210 s x) (@lem3351931 _87210 s x)). Qed.
Lemma lem3351955 {_87210 : Type'} (s : type686 _87210) : (term242 _87210 s) = (term264 _87210 s).
Proof. exact (fun_ext (fun x : _87210 => @lem3351954 _87210 s x)). Qed.
Lemma lem3351956 {_87210 : Type'} : (@ex _87210) = (@ex _87210).
Proof. exact (eq_refl (@ex _87210)). Qed.
Lemma lem3351957 {_87210 : Type'} (s : type686 _87210) : (term243 _87210 s) = (term265 _87210 s).
Proof. exact (MK_COMB (@lem3351956 _87210) (@lem3351955 _87210 s)). Qed.
Lemma lem3351958 {_87210 : Type'} (s : type686 _87210) : (term222 _87210 s) = (term265 _87210 s).
Proof. exact (TRANS (@lem3351927 _87210 s) (@lem3351957 _87210 s)). Qed.
Lemma lem3351959 {_87210 : Type'} : (term224 _87210) = (term266 _87210).
Proof. exact (fun_ext (fun s : type686 _87210 => @lem3351958 _87210 s)). Qed.
Lemma lem3351960 {_87210 : Type'} : (@ex ((_87210 -> Prop) -> Prop)) = (@ex ((_87210 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87210 -> Prop) -> Prop))). Qed.
Lemma lem3351961 {_87210 : Type'} : (term225 _87210) = (term267 _87210).
Proof. exact (MK_COMB (@lem3351960 _87210) (@lem3351959 _87210)). Qed.
Lemma lem3351962 {_87210 : Type'} : (term207 _87210) = (term267 _87210).
Proof. exact (TRANS (@lem3351900 _87210) (@lem3351961 _87210)). Qed.
Lemma lem3351963 {_87210 : Type'} : (term164 _87210) = (term267 _87210).
Proof. exact (TRANS (@lem3351873 _87210) (@lem3351962 _87210)). Qed.
Lemma lem3351964 {_87210 : Type'} : (term118 _87210) = (term267 _87210).
Proof. exact (TRANS (@lem3351814 _87210) (@lem3351963 _87210)). Qed.
Lemma lem3351965 {_87210 : Type'} : (term44 _87210) = (term267 _87210).
Proof. exact (TRANS (@lem3351168 _87210) (@lem3351964 _87210)). Qed.
Lemma lem3351966 {_87210 : Type'} (h1 : term44 _87210) : term267 _87210.
Proof. exact (EQ_MP (@lem3351965 _87210) (@lem3351075 _87210 h1)). Qed.
Lemma lem3351967 {_87210 : Type'} (x : _87210) : (term60 _87210 x) = (term60 _87210 x).
Proof. exact (eq_refl (term60 _87210 x)). Qed.
Lemma lem3351968 {_87210 : Type'} : (term61 _87210) = (term61 _87210).
Proof. exact (fun_ext (fun x : _87210 => @lem3351967 _87210 x)). Qed.
Lemma lem3351969 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3351978 {_87210 : Type'} : (term46 _87210) = (term46 _87210).
Proof. exact (MK_COMB (@lem3351969 _87210) (@lem3351968 _87210)). Qed.
Lemma lem3351979 {_87210 : Type'} (h1 : term46 _87210) : term46 _87210.
Proof. exact (EQ_MP (@lem3351978 _87210) (@lem3351076 _87210 h1)). Qed.
Lemma lem3351993 {_87210 : Type'} (s : type686 _87210) (h1 : term265 _87210 s) : term265 _87210 s.
Proof. exact (h1). Qed.
Lemma lem3351994 {_87210 : Type'} (s : type686 _87210) (x : _87210) (h1 : term263 _87210 s x) : term263 _87210 s x.
Proof. exact (h1). Qed.
Lemma lem3351995 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term260 _87210 s x t) : term260 _87210 s x t.
Proof. exact (h1). Qed.
Lemma lem3352002 {_87210 : Type'} (x : _87210) : (term60 _87210 x) = (term60 _87210 x).
Proof. exact (eq_refl (term60 _87210 x)). Qed.
Lemma lem3352003 {_87210 : Type'} : (term61 _87210) = (term61 _87210).
Proof. exact (fun_ext (fun x : _87210 => @lem3352002 _87210 x)). Qed.
Lemma lem3352004 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3352005 {_87210 : Type'} : (term46 _87210) = (term46 _87210).
Proof. exact (MK_COMB (@lem3352004 _87210) (@lem3352003 _87210)). Qed.
Lemma lem3352006 {_87210 : Type'} (h1 : term46 _87210) : term46 _87210.
Proof. exact (EQ_MP (@lem3352005 _87210) (@lem3351979 _87210 h1)). Qed.
Lemma lem3352030 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term62 _87210 s x t) = (term62 _87210 s x t).
Proof. exact (eq_refl (term62 _87210 s x t)). Qed.
Lemma lem3352057 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term70 _87210 s x t) = (term70 _87210 s x t).
Proof. exact (eq_refl (term70 _87210 s x t)). Qed.
Lemma lem3352058 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term79 _87210 s x) = (term79 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3352057 _87210 s x t)). Qed.
Lemma lem3352059 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3352060 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term80 _87210 s x) = (term80 _87210 s x).
Proof. exact (MK_COMB (@lem3352059 _87210) (@lem3352058 _87210 s x)). Qed.
Lemma lem3352061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3352062 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term91 _87210 s x) = (term91 _87210 s x).
Proof. exact (MK_COMB (@lem3352061) (@lem3352060 _87210 s x)). Qed.
Lemma lem3352063 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term199 _87210 s x t) = (term199 _87210 s x t).
Proof. exact (MK_COMB (@lem3352062 _87210 s x) (@lem3352030 _87210 s x t)). Qed.
Lemma lem3352080 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term82 _87210 s x t) = (term82 _87210 s x t).
Proof. exact (eq_refl (term82 _87210 s x t)). Qed.
Lemma lem3352081 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term88 _87210 s x) = (term88 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3352080 _87210 s x t)). Qed.
Lemma lem3352082 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3352083 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term89 _87210 s x) = (term89 _87210 s x).
Proof. exact (MK_COMB (@lem3352082 _87210) (@lem3352081 _87210 s x)). Qed.
Lemma lem3352106 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term177 _87210 s x t) = (term177 _87210 s x t).
Proof. exact (eq_refl (term177 _87210 s x t)). Qed.
Lemma lem3352107 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term179 _87210 t s x) = (term179 _87210 t s x).
Proof. exact (MK_COMB (@lem3352106 _87210 s x t) (@lem3352083 _87210 s x)). Qed.
Lemma lem3352108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3352109 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) : (term258 _87210 t s x) = (term258 _87210 t s x).
Proof. exact (MK_COMB (@lem3352108) (@lem3352107 _87210 t s x)). Qed.
Lemma lem3352110 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term260 _87210 s x t) = (term260 _87210 s x t).
Proof. exact (MK_COMB (@lem3352109 _87210 t s x) (@lem3352063 _87210 s x t)). Qed.
Lemma lem3352111 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term260 _87210 s x t) : term260 _87210 s x t.
Proof. exact (EQ_MP (@lem3352110 _87210 s x t) (@lem3351995 _87210 s x t h1)). Qed.
Lemma lem3352112 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term179 _87210 t s x.
Proof. exact (h1). Qed.
Lemma lem3352113 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term199 _87210 s x t.
Proof. exact (h1). Qed.
Lemma lem3352114 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term89 _87210 s x.
Proof. exact (proj2 (@lem3352112 _87210 t s x h1)). Qed.
Lemma lem3352115 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term31 _87210 s x t.
Proof. exact (proj1 (@lem3352112 _87210 t s x h1)). Qed.
Lemma lem3352117 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term27 _87210 t s.
Proof. exact (proj1 (@lem3352115 _87210 t s x h1)). Qed.
Lemma lem3352120 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term62 _87210 s x t.
Proof. exact (proj2 (@lem3352113 _87210 s x t h1)). Qed.
Lemma lem3352121 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term80 _87210 s x.
Proof. exact (proj1 (@lem3352113 _87210 s x t h1)). Qed.
Lemma lem3352125 {_87210 : Type'} (x : _87210) : (term60 _87210 x) = (term60 _87210 x).
Proof. exact (eq_refl (term60 _87210 x)). Qed.
Lemma lem3352126 {_87210 : Type'} : (term61 _87210) = (term61 _87210).
Proof. exact (fun_ext (fun x : _87210 => @lem3352125 _87210 x)). Qed.
Lemma lem3352127 {_87210 : Type'} : (@all _87210) = (@all _87210).
Proof. exact (eq_refl (@all _87210)). Qed.
Lemma lem3352129 {_87210 : Type'} : (term46 _87210) = (term46 _87210).
Proof. exact (MK_COMB (@lem3352127 _87210) (@lem3352126 _87210)). Qed.
Lemma lem3352130 {_87210 : Type'} (h1 : term46 _87210) : term46 _87210.
Proof. exact (EQ_MP (@lem3352129 _87210) (@lem3352006 _87210 h1)). Qed.
Lemma lem3352158 {_87210 : Type'} (t : _87210 -> Prop) (h1 : t = (@EMPTY _87210)) : t = (@EMPTY _87210).
Proof. exact (h1). Qed.
Lemma lem3352180 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term82 _87210 s x t) = (term82 _87210 s x t).
Proof. exact (eq_refl (term82 _87210 s x t)). Qed.
Lemma lem3352181 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term88 _87210 s x) = (term88 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3352180 _87210 s x t)). Qed.
Lemma lem3352182 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3352184 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term89 _87210 s x) = (term89 _87210 s x).
Proof. exact (MK_COMB (@lem3352182 _87210) (@lem3352181 _87210 s x)). Qed.
Lemma lem3352185 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term89 _87210 s x.
Proof. exact (EQ_MP (@lem3352184 _87210 s x) (@lem3352114 _87210 t s x h1)). Qed.
Lemma lem3352193 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (h1 : @IN (_87210 -> Prop) t s) : @IN (_87210 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3352225 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) : (term70 _87210 s x t) = (term268 _87210 s x t).
Proof. exact (@lem19699 (term269 _87210 t) (term270 _87210 t s) (term66 _87210 x t)). Qed.
Lemma lem3352226 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term79 _87210 s x) = (term271 _87210 s x).
Proof. exact (fun_ext (fun t : _87210 -> Prop => @lem3352225 _87210 s x t)). Qed.
Lemma lem3352227 {_87210 : Type'} : (@all (_87210 -> Prop)) = (@all (_87210 -> Prop)).
Proof. exact (eq_refl (@all (_87210 -> Prop))). Qed.
Lemma lem3352229 {_87210 : Type'} (s : type686 _87210) (x : _87210) : (term80 _87210 s x) = (term272 _87210 s x).
Proof. exact (MK_COMB (@lem3352227 _87210) (@lem3352226 _87210 s x)). Qed.
Lemma lem3352230 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term272 _87210 s x.
Proof. exact (EQ_MP (@lem3352229 _87210 s x) (@lem3352121 _87210 s x t h1)). Qed.
Lemma lem3352239 {_87210 : Type'} (_34947 : _87210) (h1 : term46 _87210) : term273 _87210 _34947.
Proof. exact (@lem3352130 _87210 h1 _34947). Qed.
Lemma lem3352240 {_87210 : Type'} (_34947 : _87210) : (term273 _87210 _34947) = (term60 _87210 _34947).
Proof. exact (eq_refl (term273 _87210 _34947)). Qed.
Lemma lem3352254 {_87210 : Type'} (_34952 : _87210 -> Prop) (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term274 _87210 s x _34952.
Proof. exact (@lem3352185 _87210 t s x h1 _34952). Qed.
Lemma lem3352255 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34952 : _87210 -> Prop) : (term274 _87210 s x _34952) = (term82 _87210 s x _34952).
Proof. exact (eq_refl (term274 _87210 s x _34952)). Qed.
Lemma lem3352263 {_87210 : Type'} (_34955 : _87210 -> Prop) (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term275 _87210 s x _34955.
Proof. exact (@lem3352230 _87210 s x t h1 _34955). Qed.
Lemma lem3352264 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34955 : _87210 -> Prop) : (term275 _87210 s x _34955) = (term268 _87210 s x _34955).
Proof. exact (eq_refl (term275 _87210 s x _34955)). Qed.
Lemma lem3352265 {_87210 : Type'} (_34955 : _87210 -> Prop) (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term268 _87210 s x _34955.
Proof. exact (EQ_MP (@lem3352264 _87210 s x _34955) (@lem3352263 _87210 _34955 s x t h1)). Qed.
Lemma lem3352279 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : @IN _87210 x t.
Proof. exact (proj2 (@lem3352115 _87210 t s x h1)). Qed.
Lemma lem3352281 {_87210 : Type'} (t : _87210 -> Prop) (h1 : t = (@EMPTY _87210)) : t = (@EMPTY _87210).
Proof. exact (h1). Qed.
Lemma lem3352291 {_87210 : Type'} (_34952 : _87210 -> Prop) (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term82 _87210 s x _34952.
Proof. exact (EQ_MP (@lem3352255 _87210 s x _34952) (@lem3352254 _87210 _34952 t s x h1)). Qed.
Lemma lem3352295 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (h1 : @IN (_87210 -> Prop) t s) : @IN (_87210 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3352315 {_87210 : Type'} (_34955 : _87210 -> Prop) (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term82 _87210 s x _34955.
Proof. exact (proj2 (@lem3352265 _87210 _34955 s x t h1)). Qed.
Lemma lem3352343 {_87210 : Type'} (_34947 : _87210) (h1 : term46 _87210) : term60 _87210 _34947.
Proof. exact (EQ_MP (@lem3352240 _87210 _34947) (@lem3352239 _87210 _34947 h1)). Qed.
Lemma lem3352372 {_87210 : Type'} (x : _87210) : (term276 _87210 x) = (term276 _87210 x).
Proof. exact (eq_refl (term276 _87210 x)). Qed.
Lemma lem3352373 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (h1 : t = (@EMPTY _87210)) : (term277 _87210 x t) = (term278 _87210 x).
Proof. exact (MK_COMB (@lem3352372 _87210 x) (@lem3352281 _87210 t h1)). Qed.
Lemma lem3352374 {_87210 : Type'} (x : _87210) : (term278 _87210 x) = (@IN _87210 x (@EMPTY _87210)).
Proof. exact (eq_refl (term278 _87210 x)). Qed.
Lemma lem3352375 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term279 _87210 x t) = (term279 _87210 x t).
Proof. exact (eq_refl (term279 _87210 x t)). Qed.
Lemma lem3352376 {_87210 : Type'} (t : _87210 -> Prop) (x : _87210) : ((term277 _87210 x t) = (term278 _87210 x)) = ((term277 _87210 x t) = (@IN _87210 x (@EMPTY _87210))).
Proof. exact (MK_COMB (@lem3352375 _87210 x t) (@lem3352374 _87210 x)). Qed.
Lemma lem3352377 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term277 _87210 x t) = (@IN _87210 x t).
Proof. exact (eq_refl (term277 _87210 x t)). Qed.
Lemma lem3352378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3352379 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term279 _87210 x t) = (term280 _87210 x t).
Proof. exact (MK_COMB (@lem3352378) (@lem3352377 _87210 x t)). Qed.
Lemma lem3352380 {_87210 : Type'} (x : _87210) : (@IN _87210 x (@EMPTY _87210)) = (@IN _87210 x (@EMPTY _87210)).
Proof. exact (eq_refl (@IN _87210 x (@EMPTY _87210))). Qed.
Lemma lem3352381 {_87210 : Type'} (t : _87210 -> Prop) (x : _87210) : ((term277 _87210 x t) = (@IN _87210 x (@EMPTY _87210))) = ((@IN _87210 x t) = (@IN _87210 x (@EMPTY _87210))).
Proof. exact (MK_COMB (@lem3352379 _87210 x t) (@lem3352380 _87210 x)). Qed.
Lemma lem3352382 {_87210 : Type'} (t : _87210 -> Prop) (x : _87210) : ((term277 _87210 x t) = (term278 _87210 x)) = ((@IN _87210 x t) = (@IN _87210 x (@EMPTY _87210))).
Proof. exact (TRANS (@lem3352376 _87210 t x) (@lem3352381 _87210 t x)). Qed.
Lemma lem3352383 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (h1 : t = (@EMPTY _87210)) : (@IN _87210 x t) = (@IN _87210 x (@EMPTY _87210)).
Proof. exact (EQ_MP (@lem3352382 _87210 t x) (@lem3352373 _87210 x t h1)). Qed.
Lemma lem3352386 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term179 _87210 t s x) (h2 : t = (@EMPTY _87210)) : @IN _87210 x (@EMPTY _87210).
Proof. exact (EQ_MP (@lem3352383 _87210 x t h2) (@lem3352279 _87210 t s x h1)). Qed.
Lemma lem3352387 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term179 _87210 t s x) (h2 : t = (@EMPTY _87210)) : term281 _87210 x.
Proof. exact (fun h0 : term60 _87210 x => @lem3352386 _87210 s x t h1 h2). Qed.
Lemma lem3352389 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352390 {_87210 : Type'} (x : _87210) : (term281 _87210 x) = (@IN _87210 x (@EMPTY _87210)).
Proof. exact (@lem3352389 (@IN _87210 x (@EMPTY _87210))). Qed.
Lemma lem3352391 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term179 _87210 t s x) (h2 : t = (@EMPTY _87210)) : @IN _87210 x (@EMPTY _87210).
Proof. exact (EQ_MP (@lem3352390 _87210 x) (@lem3352387 _87210 s x t h1 h2)). Qed.
Lemma lem3352394 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3352396 {_87210 : Type'} (_34947 : _87210) : (term60 _87210 _34947) = (term283 _87210 _34947).
Proof. exact (@lem3352394 (@IN _87210 _34947 (@EMPTY _87210))). Qed.
Lemma lem3352399 {_87210 : Type'} (_34947 : _87210) (h1 : term46 _87210) : term283 _87210 _34947.
Proof. exact (EQ_MP (@lem3352396 _87210 _34947) (@lem3352343 _87210 _34947 h1)). Qed.
Lemma lem3352400 {_87210 : Type'} (_34947 : _87210) (h1 : term46 _87210) : term283 _87210 _34947.
Proof. exact (@lem3352399 _87210 _34947 h1). Qed.
Lemma lem3352401 {_87210 : Type'} (x : _87210) (h1 : term46 _87210) : term283 _87210 x.
Proof. exact (@lem3352400 _87210 x h1). Qed.
Lemma lem3352404 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (@lem3352401 _87210 x h1 (@lem3352391 _87210 s x t h2 h3)). Qed.
Lemma lem3352405 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : term284.
Proof. exact (fun h0 : ~ False => @lem3352404 _87210 s x t h1 h2 h3). Qed.
Lemma lem3352407 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352408 : term284 = False.
Proof. exact (@lem3352407 False). Qed.
Lemma lem3352411 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (h1 : @IN (_87210 -> Prop) t s) : @IN (_87210 -> Prop) t s.
Proof. exact (h1). Qed.
Lemma lem3352412 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (h1 : @IN (_87210 -> Prop) t s) : term285 _87210 t s.
Proof. exact (fun h0 : term270 _87210 t s => @lem3352411 _87210 t s h1). Qed.
Lemma lem3352414 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352415 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term285 _87210 t s) = (@IN (_87210 -> Prop) t s).
Proof. exact (@lem3352414 (@IN (_87210 -> Prop) t s)). Qed.
Lemma lem3352416 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (h1 : @IN (_87210 -> Prop) t s) : @IN (_87210 -> Prop) t s.
Proof. exact (EQ_MP (@lem3352415 _87210 t s) (@lem3352412 _87210 t s h1)). Qed.
Lemma lem3352418 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : @IN _87210 x t.
Proof. exact (proj2 (@lem3352115 _87210 t s x h1)). Qed.
Lemma lem3352419 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term286 _87210 x t.
Proof. exact (fun h0 : term66 _87210 x t => @lem3352418 _87210 t s x h1). Qed.
Lemma lem3352421 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352422 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term286 _87210 x t) = (@IN _87210 x t).
Proof. exact (@lem3352421 (@IN _87210 x t)). Qed.
Lemma lem3352423 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : @IN _87210 x t.
Proof. exact (EQ_MP (@lem3352422 _87210 x t) (@lem3352419 _87210 t s x h1)). Qed.
Lemma lem3352425 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3352426 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34952 : _87210 -> Prop) : (term82 _87210 s x _34952) = (term81 _87210 s x _34952).
Proof. exact (@lem3352425 (@IN (_87210 -> Prop) _34952 s) (@IN _87210 x _34952)). Qed.
Lemma lem3352428 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3352429 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34952 : _87210 -> Prop) : (term81 _87210 s x _34952) = (term289 _87210 s x _34952).
Proof. exact (@lem3352428 (term62 _87210 s x _34952)). Qed.
Lemma lem3352430 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34952 : _87210 -> Prop) : (term82 _87210 s x _34952) = (term289 _87210 s x _34952).
Proof. exact (TRANS (@lem3352426 _87210 s x _34952) (@lem3352429 _87210 s x _34952)). Qed.
Lemma lem3352432 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : term62 _87210 s x t.
Proof. exact (conj (@lem3352416 _87210 t s h2) (@lem3352423 _87210 t s x h1)). Qed.
Lemma lem3352434 {_87210 : Type'} (_34952 : _87210 -> Prop) (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term289 _87210 s x _34952.
Proof. exact (EQ_MP (@lem3352430 _87210 s x _34952) (@lem3352291 _87210 _34952 t s x h1)). Qed.
Lemma lem3352435 {_87210 : Type'} (_34952 : _87210 -> Prop) (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term289 _87210 s x _34952.
Proof. exact (@lem3352434 _87210 _34952 t s x h1). Qed.
Lemma lem3352436 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term179 _87210 t s x) : term289 _87210 s x t.
Proof. exact (@lem3352435 _87210 t t s x h1). Qed.
Lemma lem3352439 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : False.
Proof. exact (@lem3352436 _87210 t s x h1 (@lem3352432 _87210 x t s h1 h2)). Qed.
Lemma lem3352440 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : term284.
Proof. exact (fun h0 : ~ False => @lem3352439 _87210 x t s h1 h2). Qed.
Lemma lem3352442 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352443 : term284 = False.
Proof. exact (@lem3352442 False). Qed.
Lemma lem3352444 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3352443) (@lem3352440 _87210 x t s h1 h2)). Qed.
Lemma lem3352490 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : @IN (_87210 -> Prop) t s.
Proof. exact (proj1 (@lem3352120 _87210 s x t h1)). Qed.
Lemma lem3352491 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term285 _87210 t s.
Proof. exact (fun h0 : term270 _87210 t s => @lem3352490 _87210 s x t h1). Qed.
Lemma lem3352493 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352494 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) : (term285 _87210 t s) = (@IN (_87210 -> Prop) t s).
Proof. exact (@lem3352493 (@IN (_87210 -> Prop) t s)). Qed.
Lemma lem3352495 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : @IN (_87210 -> Prop) t s.
Proof. exact (EQ_MP (@lem3352494 _87210 t s) (@lem3352491 _87210 s x t h1)). Qed.
Lemma lem3352497 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : @IN _87210 x t.
Proof. exact (proj2 (@lem3352120 _87210 s x t h1)). Qed.
Lemma lem3352498 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term286 _87210 x t.
Proof. exact (fun h0 : term66 _87210 x t => @lem3352497 _87210 s x t h1). Qed.
Lemma lem3352500 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352501 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) : (term286 _87210 x t) = (@IN _87210 x t).
Proof. exact (@lem3352500 (@IN _87210 x t)). Qed.
Lemma lem3352502 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : @IN _87210 x t.
Proof. exact (EQ_MP (@lem3352501 _87210 x t) (@lem3352498 _87210 s x t h1)). Qed.
Lemma lem3352504 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3352505 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34955 : _87210 -> Prop) : (term82 _87210 s x _34955) = (term81 _87210 s x _34955).
Proof. exact (@lem3352504 (@IN (_87210 -> Prop) _34955 s) (@IN _87210 x _34955)). Qed.
Lemma lem3352507 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3352508 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34955 : _87210 -> Prop) : (term81 _87210 s x _34955) = (term289 _87210 s x _34955).
Proof. exact (@lem3352507 (term62 _87210 s x _34955)). Qed.
Lemma lem3352509 {_87210 : Type'} (s : type686 _87210) (x : _87210) (_34955 : _87210 -> Prop) : (term82 _87210 s x _34955) = (term289 _87210 s x _34955).
Proof. exact (TRANS (@lem3352505 _87210 s x _34955) (@lem3352508 _87210 s x _34955)). Qed.
Lemma lem3352511 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term62 _87210 s x t.
Proof. exact (conj (@lem3352495 _87210 s x t h1) (@lem3352502 _87210 s x t h1)). Qed.
Lemma lem3352513 {_87210 : Type'} (_34955 : _87210 -> Prop) (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term289 _87210 s x _34955.
Proof. exact (EQ_MP (@lem3352509 _87210 s x _34955) (@lem3352315 _87210 _34955 s x t h1)). Qed.
Lemma lem3352514 {_87210 : Type'} (_34955 : _87210 -> Prop) (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term289 _87210 s x _34955.
Proof. exact (@lem3352513 _87210 _34955 s x t h1). Qed.
Lemma lem3352515 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term289 _87210 s x t.
Proof. exact (@lem3352514 _87210 t s x t h1). Qed.
Lemma lem3352518 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : False.
Proof. exact (@lem3352515 _87210 s x t h1 (@lem3352511 _87210 s x t h1)). Qed.
Lemma lem3352519 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : term284.
Proof. exact (fun h0 : ~ False => @lem3352518 _87210 s x t h1). Qed.
Lemma lem3352521 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3352522 : term284 = False.
Proof. exact (@lem3352521 False). Qed.
Lemma lem3352523 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term199 _87210 s x t) : False.
Proof. exact (EQ_MP (@lem3352522) (@lem3352519 _87210 s x t h1)). Qed.
Lemma lem3352524 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (EQ_MP (@lem3352408) (@lem3352405 _87210 s x t h1 h2 h3)). Qed.
Lemma lem3352525 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : (@IN (_87210 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h3 : @IN (_87210 -> Prop) t s => @lem3352444 _87210 x t s h1 h2) (fun h3 : False => @lem3352295 _87210 t s h2)). Qed.
Lemma lem3352526 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3352525 _87210 x t s h1 h2) (@lem3352295 _87210 t s h2)). Qed.
Lemma lem3352527 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : (t = (@EMPTY _87210)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY _87210) => @lem3352524 _87210 s x t h1 h2 h3) (fun h4 : False => @lem3352281 _87210 t h3)). Qed.
Lemma lem3352528 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (EQ_MP (@lem3352527 _87210 s x t h1 h2 h3) (@lem3352281 _87210 t h3)). Qed.
Lemma lem3352529 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : (@IN (_87210 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h3 : @IN (_87210 -> Prop) t s => @lem3352526 _87210 x t s h1 h2) (fun h3 : False => @lem3352193 _87210 t s h2)). Qed.
Lemma lem3352530 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3352529 _87210 x t s h1 h2) (@lem3352193 _87210 t s h2)). Qed.
Lemma lem3352531 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : (t = (@EMPTY _87210)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY _87210) => @lem3352528 _87210 s x t h1 h2 h3) (fun h4 : False => @lem3352158 _87210 t h3)). Qed.
Lemma lem3352532 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (EQ_MP (@lem3352531 _87210 s x t h1 h2 h3) (@lem3352158 _87210 t h3)). Qed.
Lemma lem3352533 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : (@IN (_87210 -> Prop) t s) = False.
Proof. exact (prop_ext (fun h3 : @IN (_87210 -> Prop) t s => @lem3352530 _87210 x t s h1 h2) (fun h3 : False => @lem3352193 _87210 t s h2)). Qed.
Lemma lem3352534 {_87210 : Type'} (x : _87210) (t : _87210 -> Prop) (s : type686 _87210) (h1 : term179 _87210 t s x) (h2 : @IN (_87210 -> Prop) t s) : False.
Proof. exact (EQ_MP (@lem3352533 _87210 x t s h1 h2) (@lem3352193 _87210 t s h2)). Qed.
Lemma lem3352535 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : (t = (@EMPTY _87210)) = False.
Proof. exact (prop_ext (fun h4 : t = (@EMPTY _87210) => @lem3352532 _87210 s x t h1 h2 h3) (fun h4 : False => @lem3352158 _87210 t h3)). Qed.
Lemma lem3352536 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (EQ_MP (@lem3352535 _87210 s x t h1 h2 h3) (@lem3352158 _87210 t h3)). Qed.
Lemma lem3352537 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : (term46 _87210) = False.
Proof. exact (prop_ext (fun h4 : term46 _87210 => @lem3352536 _87210 s x t h1 h2 h3) (fun h4 : False => @lem3352130 _87210 h1)). Qed.
Lemma lem3352538 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term179 _87210 t s x) (h3 : t = (@EMPTY _87210)) : False.
Proof. exact (EQ_MP (@lem3352537 _87210 s x t h1 h2 h3) (@lem3352130 _87210 h1)). Qed.
Lemma lem3352539 {_87210 : Type'} (t : _87210 -> Prop) (s : type686 _87210) (x : _87210) (h1 : term46 _87210) (h2 : term179 _87210 t s x) : False.
Proof. exact (or_elim (@lem3352117 _87210 t s x h2) (fun h0 : t = (@EMPTY _87210) => @lem3352538 _87210 s x t h1 h2 h0) (fun h0 : @IN (_87210 -> Prop) t s => @lem3352534 _87210 x t s h2 h0)). Qed.
Lemma lem3352540 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term260 _87210 s x t) : False.
Proof. exact (or_elim (@lem3352111 _87210 s x t h2) (fun h0 : term179 _87210 t s x => @lem3352539 _87210 t s x h1 h0) (fun h0 : term199 _87210 s x t => @lem3352523 _87210 s x t h0)). Qed.
Lemma lem3352541 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term260 _87210 s x t) : (term260 _87210 s x t) = False.
Proof. exact (prop_ext (fun h3 : term260 _87210 s x t => @lem3352540 _87210 s x t h1 h2) (fun h3 : False => @lem3352111 _87210 s x t h2)). Qed.
Lemma lem3352542 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term260 _87210 s x t) : False.
Proof. exact (EQ_MP (@lem3352541 _87210 s x t h1 h2) (@lem3352111 _87210 s x t h2)). Qed.
Lemma lem3352543 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term260 _87210 s x t) : (term46 _87210) = False.
Proof. exact (prop_ext (fun h3 : term46 _87210 => @lem3352542 _87210 s x t h1 h2) (fun h3 : False => @lem3352006 _87210 h1)). Qed.
Lemma lem3352544 {_87210 : Type'} (s : type686 _87210) (x : _87210) (t : _87210 -> Prop) (h1 : term46 _87210) (h2 : term260 _87210 s x t) : False.
Proof. exact (EQ_MP (@lem3352543 _87210 s x t h1 h2) (@lem3352006 _87210 h1)). Qed.
Lemma lem3352545 {_87210 : Type'} (s : type686 _87210) (x : _87210) (h1 : term46 _87210) (h2 : term263 _87210 s x) : False.
Proof. exact (ex_elim (@lem3351994 _87210 s x h2) (fun t : _87210 -> Prop => fun h0 : term262 _87210 s x t => @lem3352544 _87210 s x t h1 h0)). Qed.
Lemma lem3352546 {_87210 : Type'} (s : type686 _87210) (h1 : term46 _87210) (h2 : term265 _87210 s) : False.
Proof. exact (ex_elim (@lem3351993 _87210 s h2) (fun x : _87210 => fun h0 : term264 _87210 s x => @lem3352545 _87210 s x h1 h0)). Qed.
Lemma lem3352547 {_87210 : Type'} (h1 : term46 _87210) (h2 : term44 _87210) : False.
Proof. exact (ex_elim (@lem3351966 _87210 h2) (fun s : type686 _87210 => fun h0 : term266 _87210 s => @lem3352546 _87210 s h1 h0)). Qed.
Lemma lem3352548 {_87210 : Type'} (h1 : term46 _87210) (h2 : term44 _87210) : (term46 _87210) = False.
Proof. exact (prop_ext (fun h3 : term46 _87210 => @lem3352547 _87210 h1 h2) (fun h3 : False => @lem3351979 _87210 h1)). Qed.
Lemma lem3352549 {_87210 : Type'} (h1 : term46 _87210) (h2 : term44 _87210) : False.
Proof. exact (EQ_MP (@lem3352548 _87210 h1 h2) (@lem3351979 _87210 h1)). Qed.
Lemma lem3352550 {_87210 : Type'} (h1 : term46 _87210) (h2 : term44 _87210) : term51 _87210.
Proof. exact (fun h0 : term45 _87210 => @lem3352549 _87210 h1 h2). Qed.
Lemma lem3352551 {_87210 : Type'} : (term51 _87210) = (term52 _87210).
Proof. exact (@lem69 (term45 _87210)). Qed.
Lemma lem3352552 {_87210 : Type'} (h1 : term46 _87210) (h2 : term44 _87210) : term52 _87210.
Proof. exact (EQ_MP (@lem3352551 _87210) (@lem3352550 _87210 h1 h2)). Qed.
Lemma lem3352553 {_87210 : Type'} (h1 : term44 _87210) : term55 _87210.
Proof. exact (fun h0 : term46 _87210 => @lem3352552 _87210 h0 h1). Qed.
Lemma lem3352554 {_87210 : Type'} : term57 _87210.
Proof. exact (fun h0 : term44 _87210 => @lem3352553 _87210 h0). Qed.
Lemma lem3352555 {_87210 : Type'} : term47 _87210.
Proof. exact (EQ_MP (@lem3351074 _87210) (@lem3352554 _87210)). Qed.
Lemma lem3352557 {_87210 : Type'} : term47 _87210.
Proof. exact (@lem3350836 _87210 (@lem3352555 _87210)). Qed.
Lemma lem3352558 {_87210 : Type'} (h1 : term44 _87210) : term54 _87210.
Proof. exact (@lem3352557 _87210 (@lem3350817 _87210 h1)). Qed.
Lemma lem3352559 {_87210 : Type'} (h1 : term44 _87210) : term51 _87210.
Proof. exact (@lem3352558 _87210 h1 (@lem3350819 _87210)). Qed.
Lemma lem3352560 {_87210 : Type'} (h1 : term44 _87210) : False.
Proof. exact (@lem3352559 _87210 h1 (@lem3350818 _87210)). Qed.
Lemma lem3352561 {_87210 : Type'} (h1 : term44 _87210) : (term44 _87210) = False.
Proof. exact (prop_ext (fun h2 : term44 _87210 => @lem3352560 _87210 h1) (fun h2 : False => @lem3350817 _87210 h1)). Qed.
Lemma lem3352562 {_87210 : Type'} (h1 : term44 _87210) : False.
Proof. exact (EQ_MP (@lem3352561 _87210 h1) (@lem3350817 _87210 h1)). Qed.
Lemma lem3352563 {_87210 : Type'} : term43 _87210.
Proof. exact (fun h0 : term44 _87210 => @lem3352562 _87210 h0). Qed.
Lemma lem3352564 {_87210 : Type'} : term41 _87210.
Proof. exact (EQ_MP (@lem3350816 _87210) (@lem3352563 _87210)). Qed.
Lemma lem3352565 {_87210 : Type'} : term21 _87210.
Proof. exact (EQ_MP (@lem3350812 _87210) (@lem3352564 _87210)). Qed.
Lemma lem3352566 {_87210 : Type'} : term20 _87210.
Proof. exact (EQ_MP (@lem3350741 _87210) (@lem3352565 _87210)). Qed.
