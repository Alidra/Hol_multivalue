Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_DELETE_EMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_DELETE_spec.
Require Import IN_UNIONS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem3352567 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3352568 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3352569 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3352568 t1) (@lem3352567 t1)). Qed.
Lemma lem3352570 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3352569 t1 t2). Qed.
Lemma lem3352571 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3352572 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3352571 t1 t2) (@lem3352570 t1 t2)). Qed.
Lemma lem3352573 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3352572 t1 t2 t3). Qed.
Lemma lem3352574 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3352575 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3352574 t1 t2 t3) (@lem3352573 t1 t2 t3)). Qed.
Lemma lem3352576 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3352575 t1 t2 t3)). Qed.
Lemma lem3352577 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3352578 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3352579 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3352578 A s) (@lem3352577 A s)). Qed.
Lemma lem3352580 {A : Type'} (s : A -> Prop) (x : A) : term9 A s x.
Proof. exact (@lem3352579 A s x). Qed.
Lemma lem3352581 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (term10 A s x).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3352582 {A : Type'} (s : A -> Prop) (x : A) : term10 A s x.
Proof. exact (EQ_MP (@lem3352581 A s x) (@lem3352580 A s x)). Qed.
Lemma lem3352583 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term11 A s x y.
Proof. exact (@lem3352582 A s x y). Qed.
Lemma lem3352584 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A s x y) = ((term12 A x s y) = (term13 A s x y)).
Proof. exact (eq_refl (term11 A s x y)). Qed.
Lemma lem3352586 {A : Type'} (s : type686 A) : term14 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3352587 {A : Type'} (s : type686 A) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3352588 {A : Type'} (s : type686 A) : term15 A s.
Proof. exact (EQ_MP (@lem3352587 A s) (@lem3352586 A s)). Qed.
Lemma lem3352589 {A : Type'} (s : type686 A) (x : A) : term16 A s x.
Proof. exact (@lem3352588 A s x). Qed.
Lemma lem3352590 {A : Type'} (s : type686 A) (x : A) : (term16 A s x) = ((term17 A x s) = (term18 A s x)).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem3352592 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3352593 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem3352594 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem3352593 A s) (@lem3352592 A s)). Qed.
Lemma lem3352595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem3352594 A s t). Qed.
Lemma lem3352596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((s = t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem3352605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term22 A s t).
Proof. exact (EQ_MP (@lem3352596 A s t) (@lem3352595 A s t)). Qed.
Lemma lem3352606 {_87226 : Type'} (s : _87226 -> Prop) (t : _87226 -> Prop) : (s = t) = (term22 _87226 s t).
Proof. exact (@lem3352605 _87226 s t). Qed.
Lemma lem3352607 {_87226 : Type'} (s : type686 _87226) : ((term23 _87226 s) = (@UNIONS _87226 s)) = (term24 _87226 s).
Proof. exact (@lem3352606 _87226 (term23 _87226 s) (@UNIONS _87226 s)). Qed.
Lemma lem3352608 {_87226 : Type'} : (term25 _87226) = (term26 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3352607 _87226 s)). Qed.
Lemma lem3352609 {_87226 : Type'} : (@all ((_87226 -> Prop) -> Prop)) = (@all ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3352610 {_87226 : Type'} : (term27 _87226) = (term28 _87226).
Proof. exact (MK_COMB (@lem3352609 _87226) (@lem3352608 _87226)). Qed.
Lemma lem3352611 {_87226 : Type'} : (term28 _87226) = (term27 _87226).
Proof. exact (SYM (@lem3352610 _87226)). Qed.
Lemma lem3352623 {A : Type'} (s : type686 A) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (EQ_MP (@lem3352590 A s x) (@lem3352589 A s x)). Qed.
Lemma lem3352624 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term17 _87226 x s) = (term18 _87226 s x).
Proof. exact (@lem3352623 _87226 s x). Qed.
Lemma lem3352625 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term29 _87226 x s) = (term30 _87226 s x).
Proof. exact (@lem3352624 _87226 (@DELETE (_87226 -> Prop) s (@EMPTY _87226)) x). Qed.
Lemma lem3352633 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term12 A x s y) = (term13 A s x y).
Proof. exact (EQ_MP (@lem3352584 A s x y) (@lem3352583 A s x y)). Qed.
Lemma lem3352634 {_87226 : Type'} (s : type686 _87226) (x : _87226 -> Prop) (y : _87226 -> Prop) : (term31 _87226 x s y) = (term32 _87226 s x y).
Proof. exact (@lem3352633 (_87226 -> Prop) s x y). Qed.
Lemma lem3352635 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term33 _87226 t s) = (term34 _87226 s t).
Proof. exact (@lem3352634 _87226 s t (@EMPTY _87226)). Qed.
Lemma lem3352640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3352641 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term35 _87226 t s) = (term36 _87226 s t).
Proof. exact (MK_COMB (@lem3352640) (@lem3352635 _87226 s t)). Qed.
Lemma lem3352642 {_87226 : Type'} (x : _87226) (t : _87226 -> Prop) : (@IN _87226 x t) = (@IN _87226 x t).
Proof. exact (eq_refl (@IN _87226 x t)). Qed.
Lemma lem3352643 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term37 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (MK_COMB (@lem3352641 _87226 s t) (@lem3352642 _87226 x t)). Qed.
Lemma lem3352646 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term39 _87226 s x) = (term40 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352643 _87226 s x t)). Qed.
Lemma lem3352647 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3352648 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term30 _87226 s x) = (term41 _87226 s x).
Proof. exact (MK_COMB (@lem3352647 _87226) (@lem3352646 _87226 s x)). Qed.
Lemma lem3352653 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term29 _87226 x s) = (term41 _87226 s x).
Proof. exact (TRANS (@lem3352625 _87226 s x) (@lem3352648 _87226 s x)). Qed.
Lemma lem3352654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3352655 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term42 _87226 x s) = (term43 _87226 s x).
Proof. exact (MK_COMB (@lem3352654) (@lem3352653 _87226 s x)). Qed.
Lemma lem3352657 {A : Type'} (s : type686 A) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (EQ_MP (@lem3352590 A s x) (@lem3352589 A s x)). Qed.
Lemma lem3352658 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term17 _87226 x s) = (term18 _87226 s x).
Proof. exact (@lem3352657 _87226 s x). Qed.
Lemma lem3352665 {_87226 : Type'} (s : type686 _87226) (x : _87226) : ((term29 _87226 x s) = (term17 _87226 x s)) = ((term41 _87226 s x) = (term18 _87226 s x)).
Proof. exact (MK_COMB (@lem3352655 _87226 s x) (@lem3352658 _87226 s x)). Qed.
Lemma lem3352668 {_87226 : Type'} (s : type686 _87226) : (term44 _87226 s) = (term45 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3352665 _87226 s x)). Qed.
Lemma lem3352669 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3352670 {_87226 : Type'} (s : type686 _87226) : (term24 _87226 s) = (term46 _87226 s).
Proof. exact (MK_COMB (@lem3352669 _87226) (@lem3352668 _87226 s)). Qed.
Lemma lem3352675 {_87226 : Type'} : (term26 _87226) = (term47 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3352670 _87226 s)). Qed.
Lemma lem3352676 {_87226 : Type'} : (@all ((_87226 -> Prop) -> Prop)) = (@all ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3352677 {_87226 : Type'} : (term28 _87226) = (term48 _87226).
Proof. exact (MK_COMB (@lem3352676 _87226) (@lem3352675 _87226)). Qed.
Lemma lem3352682 {_87226 : Type'} : (term48 _87226) = (term28 _87226).
Proof. exact (SYM (@lem3352677 _87226)). Qed.
Lemma lem3352684 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3352685 {_87226 : Type'} : (term48 _87226) = (term50 _87226).
Proof. exact (@lem3352684 (term48 _87226)). Qed.
Lemma lem3352686 {_87226 : Type'} : (term50 _87226) = (term48 _87226).
Proof. exact (SYM (@lem3352685 _87226)). Qed.
Lemma lem3352687 {_87226 : Type'} (h1 : term51 _87226) : term51 _87226.
Proof. exact (h1). Qed.
Lemma lem3352688 {_87226 : Type'} : term52 _87226.
Proof. exact (@lem3204775 (_87226 -> Prop)). Qed.
Lemma lem3352689 {_87226 : Type'} : term53 _87226.
Proof. exact (@lem3204775 _87226). Qed.
Lemma lem3352693 {_87226 : Type'} (h1 : term54 _87226) : term54 _87226.
Proof. exact (h1). Qed.
Lemma lem3352694 {_87226 : Type'} : term55 _87226.
Proof. exact (fun h0 : term54 _87226 => @lem3352693 _87226 h0). Qed.
Lemma lem3352695 {_87226 : Type'} (h1 : term55 _87226) : term55 _87226.
Proof. exact (h1). Qed.
Lemma lem3352696 {_87226 : Type'} (h1 : term54 _87226) : term54 _87226.
Proof. exact (h1). Qed.
Lemma lem3352697 {_87226 : Type'} (h1 : term54 _87226) (h2 : term55 _87226) : term54 _87226.
Proof. exact (@lem3352695 _87226 h2 (@lem3352696 _87226 h1)). Qed.
Lemma lem3352698 {_87226 : Type'} (h1 : term54 _87226) : term56 _87226.
Proof. exact (fun h0 : term55 _87226 => @lem3352697 _87226 h1 h0). Qed.
Lemma lem3352699 {_87226 : Type'} (h1 : term55 _87226) : term55 _87226.
Proof. exact (h1). Qed.
Lemma lem3352700 {_87226 : Type'} (h1 : term54 _87226) (h2 : term55 _87226) : term54 _87226.
Proof. exact (@lem3352698 _87226 h1 (@lem3352699 _87226 h2)). Qed.
Lemma lem3352701 {_87226 : Type'} (h1 : term55 _87226) : term55 _87226.
Proof. exact (fun h0 : term54 _87226 => @lem3352700 _87226 h0 h1). Qed.
Lemma lem3352702 {_87226 : Type'} : term57 _87226.
Proof. exact (fun h0 : term55 _87226 => @lem3352701 _87226 h0). Qed.
Lemma lem3352705 {_87226 : Type'} : term55 _87226.
Proof. exact (@lem3352702 _87226 (@lem3352694 _87226)). Qed.
Lemma lem3352706 {_87226 : Type'} : term55 _87226.
Proof. exact (@lem3352705 _87226). Qed.
Lemma lem3352826 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3352827 {_87226 : Type'} : (term58 _87226) = (term59 _87226).
Proof. exact (@lem3352826 (term52 _87226)). Qed.
Lemma lem3352832 {_87226 : Type'} : (term60 _87226) = (term60 _87226).
Proof. exact (eq_refl (term60 _87226)). Qed.
Lemma lem3352833 {_87226 : Type'} : (term61 _87226) = (term62 _87226).
Proof. exact (MK_COMB (@lem3352832 _87226) (@lem3352827 _87226)). Qed.
Lemma lem3352836 {_87226 : Type'} : (term63 _87226) = (term63 _87226).
Proof. exact (eq_refl (term63 _87226)). Qed.
Lemma lem3352843 {_87226 : Type'} : (term54 _87226) = (term64 _87226).
Proof. exact (MK_COMB (@lem3352836 _87226) (@lem3352833 _87226)). Qed.
Lemma lem3352846 {_87226 : Type'} (x : _87226 -> Prop) : (term65 _87226 x) = (term65 _87226 x).
Proof. exact (eq_refl (term65 _87226 x)). Qed.
Lemma lem3352847 {_87226 : Type'} : (term66 _87226) = (term66 _87226).
Proof. exact (fun_ext (fun x : _87226 -> Prop => @lem3352846 _87226 x)). Qed.
Lemma lem3352848 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3352849 {_87226 : Type'} : (term52 _87226) = (term52 _87226).
Proof. exact (MK_COMB (@lem3352848 _87226) (@lem3352847 _87226)). Qed.
Lemma lem3352850 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3352851 {_87226 : Type'} : (term59 _87226) = (term59 _87226).
Proof. exact (MK_COMB (@lem3352850) (@lem3352849 _87226)). Qed.
Lemma lem3352854 {_87226 : Type'} (x : _87226) : (term67 _87226 x) = (term67 _87226 x).
Proof. exact (eq_refl (term67 _87226 x)). Qed.
Lemma lem3352855 {_87226 : Type'} : (term68 _87226) = (term68 _87226).
Proof. exact (fun_ext (fun x : _87226 => @lem3352854 _87226 x)). Qed.
Lemma lem3352856 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3352857 {_87226 : Type'} : (term53 _87226) = (term53 _87226).
Proof. exact (MK_COMB (@lem3352856 _87226) (@lem3352855 _87226)). Qed.
Lemma lem3352858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3352859 {_87226 : Type'} : (term60 _87226) = (term60 _87226).
Proof. exact (MK_COMB (@lem3352858) (@lem3352857 _87226)). Qed.
Lemma lem3352860 {_87226 : Type'} : (term62 _87226) = (term62 _87226).
Proof. exact (MK_COMB (@lem3352859 _87226) (@lem3352851 _87226)). Qed.
Lemma lem3352865 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term69 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term69 _87226 s x t)). Qed.
Lemma lem3352866 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term70 _87226 s x) = (term70 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352865 _87226 s x t)). Qed.
Lemma lem3352867 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3352868 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term18 _87226 s x) = (term18 _87226 s x).
Proof. exact (MK_COMB (@lem3352867 _87226) (@lem3352866 _87226 s x)). Qed.
Lemma lem3352879 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term38 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (eq_refl (term38 _87226 s x t)). Qed.
Lemma lem3352880 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term40 _87226 s x) = (term40 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352879 _87226 s x t)). Qed.
Lemma lem3352881 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3352882 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term41 _87226 s x) = (term41 _87226 s x).
Proof. exact (MK_COMB (@lem3352881 _87226) (@lem3352880 _87226 s x)). Qed.
Lemma lem3352883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3352884 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term43 _87226 s x) = (term43 _87226 s x).
Proof. exact (MK_COMB (@lem3352883) (@lem3352882 _87226 s x)). Qed.
Lemma lem3352885 {_87226 : Type'} (s : type686 _87226) (x : _87226) : ((term41 _87226 s x) = (term18 _87226 s x)) = ((term41 _87226 s x) = (term18 _87226 s x)).
Proof. exact (MK_COMB (@lem3352884 _87226 s x) (@lem3352868 _87226 s x)). Qed.
Lemma lem3352886 {_87226 : Type'} (s : type686 _87226) : (term45 _87226 s) = (term45 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3352885 _87226 s x)). Qed.
Lemma lem3352887 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3352888 {_87226 : Type'} (s : type686 _87226) : (term46 _87226 s) = (term46 _87226 s).
Proof. exact (MK_COMB (@lem3352887 _87226) (@lem3352886 _87226 s)). Qed.
Lemma lem3352889 {_87226 : Type'} : (term47 _87226) = (term47 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3352888 _87226 s)). Qed.
Lemma lem3352890 {_87226 : Type'} : (@all ((_87226 -> Prop) -> Prop)) = (@all ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3352891 {_87226 : Type'} : (term48 _87226) = (term48 _87226).
Proof. exact (MK_COMB (@lem3352890 _87226) (@lem3352889 _87226)). Qed.
Lemma lem3352892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3352893 {_87226 : Type'} : (term51 _87226) = (term51 _87226).
Proof. exact (MK_COMB (@lem3352892) (@lem3352891 _87226)). Qed.
Lemma lem3352894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3352895 {_87226 : Type'} : (term63 _87226) = (term63 _87226).
Proof. exact (MK_COMB (@lem3352894) (@lem3352893 _87226)). Qed.
Lemma lem3352896 {_87226 : Type'} : (term64 _87226) = (term64 _87226).
Proof. exact (MK_COMB (@lem3352895 _87226) (@lem3352860 _87226)). Qed.
Lemma lem3352945 {_87226 : Type'} : (term54 _87226) = (term64 _87226).
Proof. exact (TRANS (@lem3352843 _87226) (@lem3352896 _87226)). Qed.
Lemma lem3352946 {_87226 : Type'} : (term64 _87226) = (term54 _87226).
Proof. exact (SYM (@lem3352945 _87226)). Qed.
Lemma lem3352947 {_87226 : Type'} (h1 : term51 _87226) : term51 _87226.
Proof. exact (h1). Qed.
Lemma lem3352948 {_87226 : Type'} (h1 : term53 _87226) : term53 _87226.
Proof. exact (h1). Qed.
Lemma lem3352955 {_87226 : Type'} (t : _87226 -> Prop) : (term71 _87226 t) = (t = (@EMPTY _87226)).
Proof. exact (@lem16933 (t = (@EMPTY _87226))). Qed.
Lemma lem3352957 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) : (term72 _87226 t s) = (term72 _87226 t s).
Proof. exact (eq_refl (term72 _87226 t s)). Qed.
Lemma lem3352958 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term73 _87226 s t) = (term74 _87226 s t).
Proof. exact (MK_COMB (@lem3352957 _87226 t s) (@lem3352955 _87226 t)). Qed.
Lemma lem3352959 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term75 _87226 s t) = (term73 _87226 s t).
Proof. exact (@lem17045 (@IN (_87226 -> Prop) t s) (term76 _87226 t)). Qed.
Lemma lem3352960 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term75 _87226 s t) = (term74 _87226 s t).
Proof. exact (TRANS (@lem3352959 _87226 s t) (@lem3352958 _87226 s t)). Qed.
Lemma lem3352964 {_87226 : Type'} (x : _87226) (t : _87226 -> Prop) : (term77 _87226 x t) = (term77 _87226 x t).
Proof. exact (eq_refl (term77 _87226 x t)). Qed.
Lemma lem3352966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3352967 {_87226 : Type'} (s : type686 _87226) (t : _87226 -> Prop) : (term78 _87226 s t) = (term79 _87226 s t).
Proof. exact (MK_COMB (@lem3352966) (@lem3352960 _87226 s t)). Qed.
Lemma lem3352968 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term80 _87226 s x t) = (term81 _87226 s x t).
Proof. exact (MK_COMB (@lem3352967 _87226 s t) (@lem3352964 _87226 x t)). Qed.
Lemma lem3352969 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term82 _87226 s x t) = (term80 _87226 s x t).
Proof. exact (@lem17045 (term34 _87226 s t) (@IN _87226 x t)). Qed.
Lemma lem3352970 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term82 _87226 s x t) = (term81 _87226 s x t).
Proof. exact (TRANS (@lem3352969 _87226 s x t) (@lem3352968 _87226 s x t)). Qed.
Lemma lem3352973 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term38 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (eq_refl (term38 _87226 s x t)). Qed.
Lemma lem3352974 {_87226 : Type'} (P : type686 _87226) : (term83 _87226 P) = (term84 _87226 P).
Proof. exact (@lem18394 (_87226 -> Prop) P). Qed.
Lemma lem3352975 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term85 _87226 s x) = (term86 _87226 s x).
Proof. exact (@lem3352974 _87226 (term40 _87226 s x)). Qed.
Lemma lem3352976 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term87 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (eq_refl (term87 _87226 s x t)). Qed.
Lemma lem3352977 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3352978 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term88 _87226 s x t) = (term82 _87226 s x t).
Proof. exact (MK_COMB (@lem3352977) (@lem3352976 _87226 s x t)). Qed.
Lemma lem3352979 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term88 _87226 s x t) = (term81 _87226 s x t).
Proof. exact (TRANS (@lem3352978 _87226 s x t) (@lem3352970 _87226 s x t)). Qed.
Lemma lem3352980 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term89 _87226 s x) = (term90 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352979 _87226 s x t)). Qed.
Lemma lem3352981 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3352982 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term86 _87226 s x) = (term91 _87226 s x).
Proof. exact (MK_COMB (@lem3352981 _87226) (@lem3352980 _87226 s x)). Qed.
Lemma lem3352983 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term85 _87226 s x) = (term91 _87226 s x).
Proof. exact (TRANS (@lem3352975 _87226 s x) (@lem3352982 _87226 s x)). Qed.
Lemma lem3352984 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term40 _87226 s x) = (term40 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352973 _87226 s x t)). Qed.
Lemma lem3352985 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3352986 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term41 _87226 s x) = (term41 _87226 s x).
Proof. exact (MK_COMB (@lem3352985 _87226) (@lem3352984 _87226 s x)). Qed.
Lemma lem3352995 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term92 _87226 s x t) = (term93 _87226 s x t).
Proof. exact (@lem17045 (@IN (_87226 -> Prop) t s) (@IN _87226 x t)). Qed.
Lemma lem3352998 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term69 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term69 _87226 s x t)). Qed.
Lemma lem3352999 {_87226 : Type'} (P : type686 _87226) : (term83 _87226 P) = (term84 _87226 P).
Proof. exact (@lem18394 (_87226 -> Prop) P). Qed.
Lemma lem3353000 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term94 _87226 s x) = (term95 _87226 s x).
Proof. exact (@lem3352999 _87226 (term70 _87226 s x)). Qed.
Lemma lem3353001 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term96 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term96 _87226 s x t)). Qed.
Lemma lem3353002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3353003 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term97 _87226 s x t) = (term92 _87226 s x t).
Proof. exact (MK_COMB (@lem3353002) (@lem3353001 _87226 s x t)). Qed.
Lemma lem3353004 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term97 _87226 s x t) = (term93 _87226 s x t).
Proof. exact (TRANS (@lem3353003 _87226 s x t) (@lem3352995 _87226 s x t)). Qed.
Lemma lem3353005 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term98 _87226 s x) = (term99 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353004 _87226 s x t)). Qed.
Lemma lem3353006 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3353007 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term95 _87226 s x) = (term100 _87226 s x).
Proof. exact (MK_COMB (@lem3353006 _87226) (@lem3353005 _87226 s x)). Qed.
Lemma lem3353008 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term94 _87226 s x) = (term100 _87226 s x).
Proof. exact (TRANS (@lem3353000 _87226 s x) (@lem3353007 _87226 s x)). Qed.
Lemma lem3353009 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term70 _87226 s x) = (term70 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3352998 _87226 s x t)). Qed.
Lemma lem3353010 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353011 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term18 _87226 s x) = (term18 _87226 s x).
Proof. exact (MK_COMB (@lem3353010 _87226) (@lem3353009 _87226 s x)). Qed.
Lemma lem3353012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3353013 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term101 _87226 s x) = (term102 _87226 s x).
Proof. exact (MK_COMB (@lem3353012) (@lem3352983 _87226 s x)). Qed.
Lemma lem3353014 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term103 _87226 s x) = (term104 _87226 s x).
Proof. exact (MK_COMB (@lem3353013 _87226 s x) (@lem3353011 _87226 s x)). Qed.
Lemma lem3353015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3353016 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term105 _87226 s x) = (term105 _87226 s x).
Proof. exact (MK_COMB (@lem3353015) (@lem3352986 _87226 s x)). Qed.
Lemma lem3353017 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term106 _87226 s x) = (term107 _87226 s x).
Proof. exact (MK_COMB (@lem3353016 _87226 s x) (@lem3353008 _87226 s x)). Qed.
Lemma lem3353018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353019 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term108 _87226 s x) = (term109 _87226 s x).
Proof. exact (MK_COMB (@lem3353018) (@lem3353017 _87226 s x)). Qed.
Lemma lem3353020 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term110 _87226 s x) = (term111 _87226 s x).
Proof. exact (MK_COMB (@lem3353019 _87226 s x) (@lem3353014 _87226 s x)). Qed.
Lemma lem3353021 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term112 _87226 s x) = (term110 _87226 s x).
Proof. exact (@lem17646 (term41 _87226 s x) (term18 _87226 s x)). Qed.
Lemma lem3353022 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term112 _87226 s x) = (term111 _87226 s x).
Proof. exact (TRANS (@lem3353021 _87226 s x) (@lem3353020 _87226 s x)). Qed.
Lemma lem3353023 {_87226 : Type'} (P : _87226 -> Prop) : (term113 _87226 P) = (term114 _87226 P).
Proof. exact (@lem18392 _87226 P). Qed.
Lemma lem3353024 {_87226 : Type'} (s : type686 _87226) : (term115 _87226 s) = (term116 _87226 s).
Proof. exact (@lem3353023 _87226 (term45 _87226 s)). Qed.
Lemma lem3353025 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term117 _87226 s x) = ((term41 _87226 s x) = (term18 _87226 s x)).
Proof. exact (eq_refl (term117 _87226 s x)). Qed.
Lemma lem3353026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3353027 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term118 _87226 s x) = (term112 _87226 s x).
Proof. exact (MK_COMB (@lem3353026) (@lem3353025 _87226 s x)). Qed.
Lemma lem3353028 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term118 _87226 s x) = (term111 _87226 s x).
Proof. exact (TRANS (@lem3353027 _87226 s x) (@lem3353022 _87226 s x)). Qed.
Lemma lem3353029 {_87226 : Type'} (s : type686 _87226) : (term119 _87226 s) = (term120 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353028 _87226 s x)). Qed.
Lemma lem3353030 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353031 {_87226 : Type'} (s : type686 _87226) : (term116 _87226 s) = (term121 _87226 s).
Proof. exact (MK_COMB (@lem3353030 _87226) (@lem3353029 _87226 s)). Qed.
Lemma lem3353032 {_87226 : Type'} (s : type686 _87226) : (term115 _87226 s) = (term121 _87226 s).
Proof. exact (TRANS (@lem3353024 _87226 s) (@lem3353031 _87226 s)). Qed.
Lemma lem3353033 {_87226 : Type'} (P : type180 _87226) : (term122 _87226 P) = (term123 _87226 P).
Proof. exact (@lem18392 (type686 _87226) P). Qed.
Lemma lem3353034 {_87226 : Type'} : (term51 _87226) = (term124 _87226).
Proof. exact (@lem3353033 _87226 (term47 _87226)). Qed.
Lemma lem3353035 {_87226 : Type'} (s : type686 _87226) : (term125 _87226 s) = (term46 _87226 s).
Proof. exact (eq_refl (term125 _87226 s)). Qed.
Lemma lem3353036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3353037 {_87226 : Type'} (s : type686 _87226) : (term126 _87226 s) = (term115 _87226 s).
Proof. exact (MK_COMB (@lem3353036) (@lem3353035 _87226 s)). Qed.
Lemma lem3353038 {_87226 : Type'} (s : type686 _87226) : (term126 _87226 s) = (term121 _87226 s).
Proof. exact (TRANS (@lem3353037 _87226 s) (@lem3353032 _87226 s)). Qed.
Lemma lem3353039 {_87226 : Type'} : (term127 _87226) = (term128 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353038 _87226 s)). Qed.
Lemma lem3353040 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353041 {_87226 : Type'} : (term124 _87226) = (term129 _87226).
Proof. exact (MK_COMB (@lem3353040 _87226) (@lem3353039 _87226)). Qed.
Lemma lem3353042 {_87226 : Type'} : (term51 _87226) = (term129 _87226).
Proof. exact (TRANS (@lem3353034 _87226) (@lem3353041 _87226)). Qed.
Lemma lem3353048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3353049 {_87226 : Type'} (P : _87226 -> Prop) (Q : _87226 -> Prop) : (term130 _87226 P Q) = (term131 _87226 P Q).
Proof. exact (@lem3353048 _87226 P Q). Qed.
Lemma lem3353050 {_87226 : Type'} (s : type686 _87226) : (term132 _87226 s) = (term133 _87226 s).
Proof. exact (@lem3353049 _87226 (term134 _87226 s) (term135 _87226 s)). Qed.
Lemma lem3353051 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term136 _87226 s x) = (term107 _87226 s x).
Proof. exact (eq_refl (term136 _87226 s x)). Qed.
Lemma lem3353052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353053 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term137 _87226 s x) = (term109 _87226 s x).
Proof. exact (MK_COMB (@lem3353052) (@lem3353051 _87226 s x)). Qed.
Lemma lem3353054 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term138 _87226 s x) = (term104 _87226 s x).
Proof. exact (eq_refl (term138 _87226 s x)). Qed.
Lemma lem3353055 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term139 _87226 s x) = (term111 _87226 s x).
Proof. exact (MK_COMB (@lem3353053 _87226 s x) (@lem3353054 _87226 s x)). Qed.
Lemma lem3353056 {_87226 : Type'} (s : type686 _87226) : (term140 _87226 s) = (term120 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353055 _87226 s x)). Qed.
Lemma lem3353057 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353058 {_87226 : Type'} (s : type686 _87226) : (term132 _87226 s) = (term121 _87226 s).
Proof. exact (MK_COMB (@lem3353057 _87226) (@lem3353056 _87226 s)). Qed.
Lemma lem3353059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353060 {_87226 : Type'} (s : type686 _87226) : (term141 _87226 s) = (term142 _87226 s).
Proof. exact (MK_COMB (@lem3353059) (@lem3353058 _87226 s)). Qed.
Lemma lem3353061 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term136 _87226 s x) = (term107 _87226 s x).
Proof. exact (eq_refl (term136 _87226 s x)). Qed.
Lemma lem3353062 {_87226 : Type'} (s : type686 _87226) : (term143 _87226 s) = (term134 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353061 _87226 s x)). Qed.
Lemma lem3353063 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353064 {_87226 : Type'} (s : type686 _87226) : (term144 _87226 s) = (term145 _87226 s).
Proof. exact (MK_COMB (@lem3353063 _87226) (@lem3353062 _87226 s)). Qed.
Lemma lem3353065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353066 {_87226 : Type'} (s : type686 _87226) : (term146 _87226 s) = (term147 _87226 s).
Proof. exact (MK_COMB (@lem3353065) (@lem3353064 _87226 s)). Qed.
Lemma lem3353067 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term138 _87226 s x) = (term104 _87226 s x).
Proof. exact (eq_refl (term138 _87226 s x)). Qed.
Lemma lem3353068 {_87226 : Type'} (s : type686 _87226) : (term148 _87226 s) = (term135 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353067 _87226 s x)). Qed.
Lemma lem3353069 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353070 {_87226 : Type'} (s : type686 _87226) : (term149 _87226 s) = (term150 _87226 s).
Proof. exact (MK_COMB (@lem3353069 _87226) (@lem3353068 _87226 s)). Qed.
Lemma lem3353071 {_87226 : Type'} (s : type686 _87226) : (term133 _87226 s) = (term151 _87226 s).
Proof. exact (MK_COMB (@lem3353066 _87226 s) (@lem3353070 _87226 s)). Qed.
Lemma lem3353072 {_87226 : Type'} (s : type686 _87226) : ((term132 _87226 s) = (term133 _87226 s)) = ((term121 _87226 s) = (term151 _87226 s)).
Proof. exact (MK_COMB (@lem3353060 _87226 s) (@lem3353071 _87226 s)). Qed.
Lemma lem3353073 {_87226 : Type'} (s : type686 _87226) : (term121 _87226 s) = (term151 _87226 s).
Proof. exact (EQ_MP (@lem3353072 _87226 s) (@lem3353050 _87226 s)). Qed.
Lemma lem3353362 {_87226 : Type'} : (term128 _87226) = (term152 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353073 _87226 s)). Qed.
Lemma lem3353363 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353364 {_87226 : Type'} : (term129 _87226) = (term153 _87226).
Proof. exact (MK_COMB (@lem3353363 _87226) (@lem3353362 _87226)). Qed.
Lemma lem3353366 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3353367 {_87226 : Type'} (P : type180 _87226) (Q : type180 _87226) : (term154 _87226 P Q) = (term155 _87226 P Q).
Proof. exact (@lem3353366 (type686 _87226) P Q). Qed.
Lemma lem3353368 {_87226 : Type'} : (term156 _87226) = (term157 _87226).
Proof. exact (@lem3353367 _87226 (term158 _87226) (term159 _87226)). Qed.
Lemma lem3353369 {_87226 : Type'} (s : type686 _87226) : (term160 _87226 s) = (term145 _87226 s).
Proof. exact (eq_refl (term160 _87226 s)). Qed.
Lemma lem3353370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353371 {_87226 : Type'} (s : type686 _87226) : (term161 _87226 s) = (term147 _87226 s).
Proof. exact (MK_COMB (@lem3353370) (@lem3353369 _87226 s)). Qed.
Lemma lem3353372 {_87226 : Type'} (s : type686 _87226) : (term162 _87226 s) = (term150 _87226 s).
Proof. exact (eq_refl (term162 _87226 s)). Qed.
Lemma lem3353373 {_87226 : Type'} (s : type686 _87226) : (term163 _87226 s) = (term151 _87226 s).
Proof. exact (MK_COMB (@lem3353371 _87226 s) (@lem3353372 _87226 s)). Qed.
Lemma lem3353374 {_87226 : Type'} : (term164 _87226) = (term152 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353373 _87226 s)). Qed.
Lemma lem3353375 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353376 {_87226 : Type'} : (term156 _87226) = (term153 _87226).
Proof. exact (MK_COMB (@lem3353375 _87226) (@lem3353374 _87226)). Qed.
Lemma lem3353377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353378 {_87226 : Type'} : (term165 _87226) = (term166 _87226).
Proof. exact (MK_COMB (@lem3353377) (@lem3353376 _87226)). Qed.
Lemma lem3353379 {_87226 : Type'} (s : type686 _87226) : (term160 _87226 s) = (term145 _87226 s).
Proof. exact (eq_refl (term160 _87226 s)). Qed.
Lemma lem3353380 {_87226 : Type'} : (term167 _87226) = (term158 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353379 _87226 s)). Qed.
Lemma lem3353381 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353382 {_87226 : Type'} : (term168 _87226) = (term169 _87226).
Proof. exact (MK_COMB (@lem3353381 _87226) (@lem3353380 _87226)). Qed.
Lemma lem3353383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353384 {_87226 : Type'} : (term170 _87226) = (term171 _87226).
Proof. exact (MK_COMB (@lem3353383) (@lem3353382 _87226)). Qed.
Lemma lem3353385 {_87226 : Type'} (s : type686 _87226) : (term162 _87226 s) = (term150 _87226 s).
Proof. exact (eq_refl (term162 _87226 s)). Qed.
Lemma lem3353386 {_87226 : Type'} : (term172 _87226) = (term159 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353385 _87226 s)). Qed.
Lemma lem3353387 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353388 {_87226 : Type'} : (term173 _87226) = (term174 _87226).
Proof. exact (MK_COMB (@lem3353387 _87226) (@lem3353386 _87226)). Qed.
Lemma lem3353389 {_87226 : Type'} : (term157 _87226) = (term175 _87226).
Proof. exact (MK_COMB (@lem3353384 _87226) (@lem3353388 _87226)). Qed.
Lemma lem3353390 {_87226 : Type'} : ((term156 _87226) = (term157 _87226)) = ((term153 _87226) = (term175 _87226)).
Proof. exact (MK_COMB (@lem3353378 _87226) (@lem3353389 _87226)). Qed.
Lemma lem3353391 {_87226 : Type'} : (term153 _87226) = (term175 _87226).
Proof. exact (EQ_MP (@lem3353390 _87226) (@lem3353368 _87226)). Qed.
Lemma lem3353688 {_87226 : Type'} : (term129 _87226) = (term175 _87226).
Proof. exact (TRANS (@lem3353364 _87226) (@lem3353391 _87226)). Qed.
Lemma lem3353690 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3353691 {_87226 : Type'} (P : type686 _87226) (Q : Prop) : (term178 _87226 P Q) = (term179 _87226 P Q).
Proof. exact (@lem3353690 (_87226 -> Prop) P Q). Qed.
Lemma lem3353692 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term180 _87226 s x) = (term181 _87226 s x).
Proof. exact (@lem3353691 _87226 (term40 _87226 s x) (term100 _87226 s x)). Qed.
Lemma lem3353693 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term87 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (eq_refl (term87 _87226 s x t)). Qed.
Lemma lem3353694 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term182 _87226 s x) = (term40 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353693 _87226 s x t)). Qed.
Lemma lem3353695 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353696 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term183 _87226 s x) = (term41 _87226 s x).
Proof. exact (MK_COMB (@lem3353695 _87226) (@lem3353694 _87226 s x)). Qed.
Lemma lem3353697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3353698 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term184 _87226 s x) = (term105 _87226 s x).
Proof. exact (MK_COMB (@lem3353697) (@lem3353696 _87226 s x)). Qed.
Lemma lem3353699 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term100 _87226 s x) = (term100 _87226 s x).
Proof. exact (eq_refl (term100 _87226 s x)). Qed.
Lemma lem3353700 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term180 _87226 s x) = (term107 _87226 s x).
Proof. exact (MK_COMB (@lem3353698 _87226 s x) (@lem3353699 _87226 s x)). Qed.
Lemma lem3353701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353702 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term185 _87226 s x) = (term186 _87226 s x).
Proof. exact (MK_COMB (@lem3353701) (@lem3353700 _87226 s x)). Qed.
Lemma lem3353703 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term87 _87226 s x t) = (term38 _87226 s x t).
Proof. exact (eq_refl (term87 _87226 s x t)). Qed.
Lemma lem3353704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3353705 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term187 _87226 s x t) = (term188 _87226 s x t).
Proof. exact (MK_COMB (@lem3353704) (@lem3353703 _87226 s x t)). Qed.
Lemma lem3353706 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term100 _87226 s x) = (term100 _87226 s x).
Proof. exact (eq_refl (term100 _87226 s x)). Qed.
Lemma lem3353707 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term189 _87226 t s x) = (term190 _87226 t s x).
Proof. exact (MK_COMB (@lem3353705 _87226 s x t) (@lem3353706 _87226 s x)). Qed.
Lemma lem3353708 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term191 _87226 s x) = (term192 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353707 _87226 t s x)). Qed.
Lemma lem3353709 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353710 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term181 _87226 s x) = (term193 _87226 s x).
Proof. exact (MK_COMB (@lem3353709 _87226) (@lem3353708 _87226 s x)). Qed.
Lemma lem3353711 {_87226 : Type'} (s : type686 _87226) (x : _87226) : ((term180 _87226 s x) = (term181 _87226 s x)) = ((term107 _87226 s x) = (term193 _87226 s x)).
Proof. exact (MK_COMB (@lem3353702 _87226 s x) (@lem3353710 _87226 s x)). Qed.
Lemma lem3353712 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term107 _87226 s x) = (term193 _87226 s x).
Proof. exact (EQ_MP (@lem3353711 _87226 s x) (@lem3353692 _87226 s x)). Qed.
Lemma lem3353713 {_87226 : Type'} (s : type686 _87226) : (term134 _87226 s) = (term194 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353712 _87226 s x)). Qed.
Lemma lem3353714 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353715 {_87226 : Type'} (s : type686 _87226) : (term145 _87226 s) = (term195 _87226 s).
Proof. exact (MK_COMB (@lem3353714 _87226) (@lem3353713 _87226 s)). Qed.
Lemma lem3353716 {_87226 : Type'} : (term158 _87226) = (term196 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353715 _87226 s)). Qed.
Lemma lem3353717 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353718 {_87226 : Type'} : (term169 _87226) = (term197 _87226).
Proof. exact (MK_COMB (@lem3353717 _87226) (@lem3353716 _87226)). Qed.
Lemma lem3353719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353720 {_87226 : Type'} : (term171 _87226) = (term198 _87226).
Proof. exact (MK_COMB (@lem3353719) (@lem3353718 _87226)). Qed.
Lemma lem3353722 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3353723 {_87226 : Type'} (P : Prop) (Q : type686 _87226) : (term201 _87226 P Q) = (term202 _87226 P Q).
Proof. exact (@lem3353722 (_87226 -> Prop) P Q). Qed.
Lemma lem3353724 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term203 _87226 s x) = (term204 _87226 s x).
Proof. exact (@lem3353723 _87226 (term91 _87226 s x) (term70 _87226 s x)). Qed.
Lemma lem3353725 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term96 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term96 _87226 s x t)). Qed.
Lemma lem3353726 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term205 _87226 s x) = (term70 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353725 _87226 s x t)). Qed.
Lemma lem3353727 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353728 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term206 _87226 s x) = (term18 _87226 s x).
Proof. exact (MK_COMB (@lem3353727 _87226) (@lem3353726 _87226 s x)). Qed.
Lemma lem3353729 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term102 _87226 s x) = (term102 _87226 s x).
Proof. exact (eq_refl (term102 _87226 s x)). Qed.
Lemma lem3353730 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term203 _87226 s x) = (term104 _87226 s x).
Proof. exact (MK_COMB (@lem3353729 _87226 s x) (@lem3353728 _87226 s x)). Qed.
Lemma lem3353731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353732 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term207 _87226 s x) = (term208 _87226 s x).
Proof. exact (MK_COMB (@lem3353731) (@lem3353730 _87226 s x)). Qed.
Lemma lem3353733 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term96 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term96 _87226 s x t)). Qed.
Lemma lem3353734 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term102 _87226 s x) = (term102 _87226 s x).
Proof. exact (eq_refl (term102 _87226 s x)). Qed.
Lemma lem3353735 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term209 _87226 s x t) = (term210 _87226 s x t).
Proof. exact (MK_COMB (@lem3353734 _87226 s x) (@lem3353733 _87226 s x t)). Qed.
Lemma lem3353736 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term211 _87226 s x) = (term212 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353735 _87226 s x t)). Qed.
Lemma lem3353737 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353738 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term204 _87226 s x) = (term213 _87226 s x).
Proof. exact (MK_COMB (@lem3353737 _87226) (@lem3353736 _87226 s x)). Qed.
Lemma lem3353739 {_87226 : Type'} (s : type686 _87226) (x : _87226) : ((term203 _87226 s x) = (term204 _87226 s x)) = ((term104 _87226 s x) = (term213 _87226 s x)).
Proof. exact (MK_COMB (@lem3353732 _87226 s x) (@lem3353738 _87226 s x)). Qed.
Lemma lem3353740 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term104 _87226 s x) = (term213 _87226 s x).
Proof. exact (EQ_MP (@lem3353739 _87226 s x) (@lem3353724 _87226 s x)). Qed.
Lemma lem3353741 {_87226 : Type'} (s : type686 _87226) : (term135 _87226 s) = (term214 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353740 _87226 s x)). Qed.
Lemma lem3353742 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353743 {_87226 : Type'} (s : type686 _87226) : (term150 _87226 s) = (term215 _87226 s).
Proof. exact (MK_COMB (@lem3353742 _87226) (@lem3353741 _87226 s)). Qed.
Lemma lem3353744 {_87226 : Type'} : (term159 _87226) = (term216 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353743 _87226 s)). Qed.
Lemma lem3353745 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353746 {_87226 : Type'} : (term174 _87226) = (term217 _87226).
Proof. exact (MK_COMB (@lem3353745 _87226) (@lem3353744 _87226)). Qed.
Lemma lem3353747 {_87226 : Type'} : (term175 _87226) = (term218 _87226).
Proof. exact (MK_COMB (@lem3353720 _87226) (@lem3353746 _87226)). Qed.
Lemma lem3353749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3353750 {_87226 : Type'} (P : type180 _87226) (Q : type180 _87226) : (term155 _87226 P Q) = (term154 _87226 P Q).
Proof. exact (@lem3353749 (type686 _87226) P Q). Qed.
Lemma lem3353751 {_87226 : Type'} : (term219 _87226) = (term220 _87226).
Proof. exact (@lem3353750 _87226 (term196 _87226) (term216 _87226)). Qed.
Lemma lem3353752 {_87226 : Type'} (s : type686 _87226) : (term221 _87226 s) = (term195 _87226 s).
Proof. exact (eq_refl (term221 _87226 s)). Qed.
Lemma lem3353753 {_87226 : Type'} : (term222 _87226) = (term196 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353752 _87226 s)). Qed.
Lemma lem3353754 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353755 {_87226 : Type'} : (term223 _87226) = (term197 _87226).
Proof. exact (MK_COMB (@lem3353754 _87226) (@lem3353753 _87226)). Qed.
Lemma lem3353756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353757 {_87226 : Type'} : (term224 _87226) = (term198 _87226).
Proof. exact (MK_COMB (@lem3353756) (@lem3353755 _87226)). Qed.
Lemma lem3353758 {_87226 : Type'} (s : type686 _87226) : (term225 _87226 s) = (term215 _87226 s).
Proof. exact (eq_refl (term225 _87226 s)). Qed.
Lemma lem3353759 {_87226 : Type'} : (term226 _87226) = (term216 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353758 _87226 s)). Qed.
Lemma lem3353760 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353761 {_87226 : Type'} : (term227 _87226) = (term217 _87226).
Proof. exact (MK_COMB (@lem3353760 _87226) (@lem3353759 _87226)). Qed.
Lemma lem3353762 {_87226 : Type'} : (term219 _87226) = (term218 _87226).
Proof. exact (MK_COMB (@lem3353757 _87226) (@lem3353761 _87226)). Qed.
Lemma lem3353763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353764 {_87226 : Type'} : (term228 _87226) = (term229 _87226).
Proof. exact (MK_COMB (@lem3353763) (@lem3353762 _87226)). Qed.
Lemma lem3353765 {_87226 : Type'} (s : type686 _87226) : (term221 _87226 s) = (term195 _87226 s).
Proof. exact (eq_refl (term221 _87226 s)). Qed.
Lemma lem3353766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353767 {_87226 : Type'} (s : type686 _87226) : (term230 _87226 s) = (term231 _87226 s).
Proof. exact (MK_COMB (@lem3353766) (@lem3353765 _87226 s)). Qed.
Lemma lem3353768 {_87226 : Type'} (s : type686 _87226) : (term225 _87226 s) = (term215 _87226 s).
Proof. exact (eq_refl (term225 _87226 s)). Qed.
Lemma lem3353769 {_87226 : Type'} (s : type686 _87226) : (term232 _87226 s) = (term233 _87226 s).
Proof. exact (MK_COMB (@lem3353767 _87226 s) (@lem3353768 _87226 s)). Qed.
Lemma lem3353770 {_87226 : Type'} : (term234 _87226) = (term235 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353769 _87226 s)). Qed.
Lemma lem3353771 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353772 {_87226 : Type'} : (term220 _87226) = (term236 _87226).
Proof. exact (MK_COMB (@lem3353771 _87226) (@lem3353770 _87226)). Qed.
Lemma lem3353773 {_87226 : Type'} : ((term219 _87226) = (term220 _87226)) = ((term218 _87226) = (term236 _87226)).
Proof. exact (MK_COMB (@lem3353764 _87226) (@lem3353772 _87226)). Qed.
Lemma lem3353774 {_87226 : Type'} : (term218 _87226) = (term236 _87226).
Proof. exact (EQ_MP (@lem3353773 _87226) (@lem3353751 _87226)). Qed.
Lemma lem3353776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3353777 {_87226 : Type'} (P : _87226 -> Prop) (Q : _87226 -> Prop) : (term131 _87226 P Q) = (term130 _87226 P Q).
Proof. exact (@lem3353776 _87226 P Q). Qed.
Lemma lem3353778 {_87226 : Type'} (s : type686 _87226) : (term237 _87226 s) = (term238 _87226 s).
Proof. exact (@lem3353777 _87226 (term194 _87226 s) (term214 _87226 s)). Qed.
Lemma lem3353779 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term239 _87226 s x) = (term193 _87226 s x).
Proof. exact (eq_refl (term239 _87226 s x)). Qed.
Lemma lem3353780 {_87226 : Type'} (s : type686 _87226) : (term240 _87226 s) = (term194 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353779 _87226 s x)). Qed.
Lemma lem3353781 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353782 {_87226 : Type'} (s : type686 _87226) : (term241 _87226 s) = (term195 _87226 s).
Proof. exact (MK_COMB (@lem3353781 _87226) (@lem3353780 _87226 s)). Qed.
Lemma lem3353783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353784 {_87226 : Type'} (s : type686 _87226) : (term242 _87226 s) = (term231 _87226 s).
Proof. exact (MK_COMB (@lem3353783) (@lem3353782 _87226 s)). Qed.
Lemma lem3353785 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term243 _87226 s x) = (term213 _87226 s x).
Proof. exact (eq_refl (term243 _87226 s x)). Qed.
Lemma lem3353786 {_87226 : Type'} (s : type686 _87226) : (term244 _87226 s) = (term214 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353785 _87226 s x)). Qed.
Lemma lem3353787 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353788 {_87226 : Type'} (s : type686 _87226) : (term245 _87226 s) = (term215 _87226 s).
Proof. exact (MK_COMB (@lem3353787 _87226) (@lem3353786 _87226 s)). Qed.
Lemma lem3353789 {_87226 : Type'} (s : type686 _87226) : (term237 _87226 s) = (term233 _87226 s).
Proof. exact (MK_COMB (@lem3353784 _87226 s) (@lem3353788 _87226 s)). Qed.
Lemma lem3353790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353791 {_87226 : Type'} (s : type686 _87226) : (term246 _87226 s) = (term247 _87226 s).
Proof. exact (MK_COMB (@lem3353790) (@lem3353789 _87226 s)). Qed.
Lemma lem3353792 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term239 _87226 s x) = (term193 _87226 s x).
Proof. exact (eq_refl (term239 _87226 s x)). Qed.
Lemma lem3353793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353794 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term248 _87226 s x) = (term249 _87226 s x).
Proof. exact (MK_COMB (@lem3353793) (@lem3353792 _87226 s x)). Qed.
Lemma lem3353795 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term243 _87226 s x) = (term213 _87226 s x).
Proof. exact (eq_refl (term243 _87226 s x)). Qed.
Lemma lem3353796 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term250 _87226 s x) = (term251 _87226 s x).
Proof. exact (MK_COMB (@lem3353794 _87226 s x) (@lem3353795 _87226 s x)). Qed.
Lemma lem3353797 {_87226 : Type'} (s : type686 _87226) : (term252 _87226 s) = (term253 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353796 _87226 s x)). Qed.
Lemma lem3353798 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353799 {_87226 : Type'} (s : type686 _87226) : (term238 _87226 s) = (term254 _87226 s).
Proof. exact (MK_COMB (@lem3353798 _87226) (@lem3353797 _87226 s)). Qed.
Lemma lem3353800 {_87226 : Type'} (s : type686 _87226) : ((term237 _87226 s) = (term238 _87226 s)) = ((term233 _87226 s) = (term254 _87226 s)).
Proof. exact (MK_COMB (@lem3353791 _87226 s) (@lem3353799 _87226 s)). Qed.
Lemma lem3353801 {_87226 : Type'} (s : type686 _87226) : (term233 _87226 s) = (term254 _87226 s).
Proof. exact (EQ_MP (@lem3353800 _87226 s) (@lem3353778 _87226 s)). Qed.
Lemma lem3353803 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3353804 {_87226 : Type'} (P : type686 _87226) (Q : type686 _87226) : (term255 _87226 P Q) = (term256 _87226 P Q).
Proof. exact (@lem3353803 (_87226 -> Prop) P Q). Qed.
Lemma lem3353805 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term257 _87226 s x) = (term258 _87226 s x).
Proof. exact (@lem3353804 _87226 (term192 _87226 s x) (term212 _87226 s x)). Qed.
Lemma lem3353806 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term259 _87226 s x t) = (term190 _87226 t s x).
Proof. exact (eq_refl (term259 _87226 s x t)). Qed.
Lemma lem3353807 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term260 _87226 s x) = (term192 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353806 _87226 t s x)). Qed.
Lemma lem3353808 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353809 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term261 _87226 s x) = (term193 _87226 s x).
Proof. exact (MK_COMB (@lem3353808 _87226) (@lem3353807 _87226 s x)). Qed.
Lemma lem3353810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353811 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term262 _87226 s x) = (term249 _87226 s x).
Proof. exact (MK_COMB (@lem3353810) (@lem3353809 _87226 s x)). Qed.
Lemma lem3353812 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term263 _87226 s x t) = (term210 _87226 s x t).
Proof. exact (eq_refl (term263 _87226 s x t)). Qed.
Lemma lem3353813 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term264 _87226 s x) = (term212 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353812 _87226 s x t)). Qed.
Lemma lem3353814 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353815 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term265 _87226 s x) = (term213 _87226 s x).
Proof. exact (MK_COMB (@lem3353814 _87226) (@lem3353813 _87226 s x)). Qed.
Lemma lem3353816 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term257 _87226 s x) = (term251 _87226 s x).
Proof. exact (MK_COMB (@lem3353811 _87226 s x) (@lem3353815 _87226 s x)). Qed.
Lemma lem3353817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3353818 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term266 _87226 s x) = (term267 _87226 s x).
Proof. exact (MK_COMB (@lem3353817) (@lem3353816 _87226 s x)). Qed.
Lemma lem3353819 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term259 _87226 s x t) = (term190 _87226 t s x).
Proof. exact (eq_refl (term259 _87226 s x t)). Qed.
Lemma lem3353820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353821 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term268 _87226 s x t) = (term269 _87226 t s x).
Proof. exact (MK_COMB (@lem3353820) (@lem3353819 _87226 t s x)). Qed.
Lemma lem3353822 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term263 _87226 s x t) = (term210 _87226 s x t).
Proof. exact (eq_refl (term263 _87226 s x t)). Qed.
Lemma lem3353823 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term270 _87226 s x t) = (term271 _87226 s x t).
Proof. exact (MK_COMB (@lem3353821 _87226 t s x) (@lem3353822 _87226 s x t)). Qed.
Lemma lem3353824 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term272 _87226 s x) = (term273 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353823 _87226 s x t)). Qed.
Lemma lem3353825 {_87226 : Type'} : (@ex (_87226 -> Prop)) = (@ex (_87226 -> Prop)).
Proof. exact (eq_refl (@ex (_87226 -> Prop))). Qed.
Lemma lem3353826 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term258 _87226 s x) = (term274 _87226 s x).
Proof. exact (MK_COMB (@lem3353825 _87226) (@lem3353824 _87226 s x)). Qed.
Lemma lem3353827 {_87226 : Type'} (s : type686 _87226) (x : _87226) : ((term257 _87226 s x) = (term258 _87226 s x)) = ((term251 _87226 s x) = (term274 _87226 s x)).
Proof. exact (MK_COMB (@lem3353818 _87226 s x) (@lem3353826 _87226 s x)). Qed.
Lemma lem3353828 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term251 _87226 s x) = (term274 _87226 s x).
Proof. exact (EQ_MP (@lem3353827 _87226 s x) (@lem3353805 _87226 s x)). Qed.
Lemma lem3353829 {_87226 : Type'} (s : type686 _87226) : (term253 _87226 s) = (term275 _87226 s).
Proof. exact (fun_ext (fun x : _87226 => @lem3353828 _87226 s x)). Qed.
Lemma lem3353830 {_87226 : Type'} : (@ex _87226) = (@ex _87226).
Proof. exact (eq_refl (@ex _87226)). Qed.
Lemma lem3353831 {_87226 : Type'} (s : type686 _87226) : (term254 _87226 s) = (term276 _87226 s).
Proof. exact (MK_COMB (@lem3353830 _87226) (@lem3353829 _87226 s)). Qed.
Lemma lem3353832 {_87226 : Type'} (s : type686 _87226) : (term233 _87226 s) = (term276 _87226 s).
Proof. exact (TRANS (@lem3353801 _87226 s) (@lem3353831 _87226 s)). Qed.
Lemma lem3353833 {_87226 : Type'} : (term235 _87226) = (term277 _87226).
Proof. exact (fun_ext (fun s : type686 _87226 => @lem3353832 _87226 s)). Qed.
Lemma lem3353834 {_87226 : Type'} : (@ex ((_87226 -> Prop) -> Prop)) = (@ex ((_87226 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_87226 -> Prop) -> Prop))). Qed.
Lemma lem3353835 {_87226 : Type'} : (term236 _87226) = (term278 _87226).
Proof. exact (MK_COMB (@lem3353834 _87226) (@lem3353833 _87226)). Qed.
Lemma lem3353836 {_87226 : Type'} : (term218 _87226) = (term278 _87226).
Proof. exact (TRANS (@lem3353774 _87226) (@lem3353835 _87226)). Qed.
Lemma lem3353837 {_87226 : Type'} : (term175 _87226) = (term278 _87226).
Proof. exact (TRANS (@lem3353747 _87226) (@lem3353836 _87226)). Qed.
Lemma lem3353838 {_87226 : Type'} : (term129 _87226) = (term278 _87226).
Proof. exact (TRANS (@lem3353688 _87226) (@lem3353837 _87226)). Qed.
Lemma lem3353839 {_87226 : Type'} : (term51 _87226) = (term278 _87226).
Proof. exact (TRANS (@lem3353042 _87226) (@lem3353838 _87226)). Qed.
Lemma lem3353840 {_87226 : Type'} (h1 : term51 _87226) : term278 _87226.
Proof. exact (EQ_MP (@lem3353839 _87226) (@lem3352947 _87226 h1)). Qed.
Lemma lem3353841 {_87226 : Type'} (x : _87226) : (term67 _87226 x) = (term67 _87226 x).
Proof. exact (eq_refl (term67 _87226 x)). Qed.
Lemma lem3353842 {_87226 : Type'} : (term68 _87226) = (term68 _87226).
Proof. exact (fun_ext (fun x : _87226 => @lem3353841 _87226 x)). Qed.
Lemma lem3353843 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3353852 {_87226 : Type'} : (term53 _87226) = (term53 _87226).
Proof. exact (MK_COMB (@lem3353843 _87226) (@lem3353842 _87226)). Qed.
Lemma lem3353853 {_87226 : Type'} (h1 : term53 _87226) : term53 _87226.
Proof. exact (EQ_MP (@lem3353852 _87226) (@lem3352948 _87226 h1)). Qed.
Lemma lem3353867 {_87226 : Type'} (s : type686 _87226) (h1 : term276 _87226 s) : term276 _87226 s.
Proof. exact (h1). Qed.
Lemma lem3353868 {_87226 : Type'} (s : type686 _87226) (x : _87226) (h1 : term274 _87226 s x) : term274 _87226 s x.
Proof. exact (h1). Qed.
Lemma lem3353869 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term271 _87226 s x t) : term271 _87226 s x t.
Proof. exact (h1). Qed.
Lemma lem3353876 {_87226 : Type'} (x : _87226) : (term67 _87226 x) = (term67 _87226 x).
Proof. exact (eq_refl (term67 _87226 x)). Qed.
Lemma lem3353877 {_87226 : Type'} : (term68 _87226) = (term68 _87226).
Proof. exact (fun_ext (fun x : _87226 => @lem3353876 _87226 x)). Qed.
Lemma lem3353878 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3353879 {_87226 : Type'} : (term53 _87226) = (term53 _87226).
Proof. exact (MK_COMB (@lem3353878 _87226) (@lem3353877 _87226)). Qed.
Lemma lem3353880 {_87226 : Type'} (h1 : term53 _87226) : term53 _87226.
Proof. exact (EQ_MP (@lem3353879 _87226) (@lem3353853 _87226 h1)). Qed.
Lemma lem3353904 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term69 _87226 s x t) = (term69 _87226 s x t).
Proof. exact (eq_refl (term69 _87226 s x t)). Qed.
Lemma lem3353929 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term81 _87226 s x t) = (term81 _87226 s x t).
Proof. exact (eq_refl (term81 _87226 s x t)). Qed.
Lemma lem3353930 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term90 _87226 s x) = (term90 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353929 _87226 s x t)). Qed.
Lemma lem3353931 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3353932 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term91 _87226 s x) = (term91 _87226 s x).
Proof. exact (MK_COMB (@lem3353931 _87226) (@lem3353930 _87226 s x)). Qed.
Lemma lem3353933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3353934 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term102 _87226 s x) = (term102 _87226 s x).
Proof. exact (MK_COMB (@lem3353933) (@lem3353932 _87226 s x)). Qed.
Lemma lem3353935 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term210 _87226 s x t) = (term210 _87226 s x t).
Proof. exact (MK_COMB (@lem3353934 _87226 s x) (@lem3353904 _87226 s x t)). Qed.
Lemma lem3353952 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term93 _87226 s x t) = (term93 _87226 s x t).
Proof. exact (eq_refl (term93 _87226 s x t)). Qed.
Lemma lem3353953 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term99 _87226 s x) = (term99 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3353952 _87226 s x t)). Qed.
Lemma lem3353954 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3353955 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term100 _87226 s x) = (term100 _87226 s x).
Proof. exact (MK_COMB (@lem3353954 _87226) (@lem3353953 _87226 s x)). Qed.
Lemma lem3353980 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term188 _87226 s x t) = (term188 _87226 s x t).
Proof. exact (eq_refl (term188 _87226 s x t)). Qed.
Lemma lem3353981 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term190 _87226 t s x) = (term190 _87226 t s x).
Proof. exact (MK_COMB (@lem3353980 _87226 s x t) (@lem3353955 _87226 s x)). Qed.
Lemma lem3353982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3353983 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) : (term269 _87226 t s x) = (term269 _87226 t s x).
Proof. exact (MK_COMB (@lem3353982) (@lem3353981 _87226 t s x)). Qed.
Lemma lem3353984 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term271 _87226 s x t) = (term271 _87226 s x t).
Proof. exact (MK_COMB (@lem3353983 _87226 t s x) (@lem3353935 _87226 s x t)). Qed.
Lemma lem3353985 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term271 _87226 s x t) : term271 _87226 s x t.
Proof. exact (EQ_MP (@lem3353984 _87226 s x t) (@lem3353869 _87226 s x t h1)). Qed.
Lemma lem3353986 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term190 _87226 t s x.
Proof. exact (h1). Qed.
Lemma lem3353987 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term210 _87226 s x t.
Proof. exact (h1). Qed.
Lemma lem3353988 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term100 _87226 s x.
Proof. exact (proj2 (@lem3353986 _87226 t s x h1)). Qed.
Lemma lem3353989 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term38 _87226 s x t.
Proof. exact (proj1 (@lem3353986 _87226 t s x h1)). Qed.
Lemma lem3353991 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term34 _87226 s t.
Proof. exact (proj1 (@lem3353989 _87226 t s x h1)). Qed.
Lemma lem3353994 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term69 _87226 s x t.
Proof. exact (proj2 (@lem3353987 _87226 s x t h1)). Qed.
Lemma lem3353995 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term91 _87226 s x.
Proof. exact (proj1 (@lem3353987 _87226 s x t h1)). Qed.
Lemma lem3354019 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term93 _87226 s x t) = (term93 _87226 s x t).
Proof. exact (eq_refl (term93 _87226 s x t)). Qed.
Lemma lem3354020 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term99 _87226 s x) = (term99 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3354019 _87226 s x t)). Qed.
Lemma lem3354021 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3354023 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term100 _87226 s x) = (term100 _87226 s x).
Proof. exact (MK_COMB (@lem3354021 _87226) (@lem3354020 _87226 s x)). Qed.
Lemma lem3354024 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term100 _87226 s x.
Proof. exact (EQ_MP (@lem3354023 _87226 s x) (@lem3353988 _87226 t s x h1)). Qed.
Lemma lem3354038 {_87226 : Type'} (x : _87226) : (term67 _87226 x) = (term67 _87226 x).
Proof. exact (eq_refl (term67 _87226 x)). Qed.
Lemma lem3354039 {_87226 : Type'} : (term68 _87226) = (term68 _87226).
Proof. exact (fun_ext (fun x : _87226 => @lem3354038 _87226 x)). Qed.
Lemma lem3354040 {_87226 : Type'} : (@all _87226) = (@all _87226).
Proof. exact (eq_refl (@all _87226)). Qed.
Lemma lem3354042 {_87226 : Type'} : (term53 _87226) = (term53 _87226).
Proof. exact (MK_COMB (@lem3354040 _87226) (@lem3354039 _87226)). Qed.
Lemma lem3354043 {_87226 : Type'} (h1 : term53 _87226) : term53 _87226.
Proof. exact (EQ_MP (@lem3354042 _87226) (@lem3353880 _87226 h1)). Qed.
Lemma lem3354064 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) : (term81 _87226 s x t) = (term81 _87226 s x t).
Proof. exact (eq_refl (term81 _87226 s x t)). Qed.
Lemma lem3354065 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term90 _87226 s x) = (term90 _87226 s x).
Proof. exact (fun_ext (fun t : _87226 -> Prop => @lem3354064 _87226 s x t)). Qed.
Lemma lem3354066 {_87226 : Type'} : (@all (_87226 -> Prop)) = (@all (_87226 -> Prop)).
Proof. exact (eq_refl (@all (_87226 -> Prop))). Qed.
Lemma lem3354068 {_87226 : Type'} (s : type686 _87226) (x : _87226) : (term91 _87226 s x) = (term91 _87226 s x).
Proof. exact (MK_COMB (@lem3354066 _87226) (@lem3354065 _87226 s x)). Qed.
Lemma lem3354069 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term91 _87226 s x.
Proof. exact (EQ_MP (@lem3354068 _87226 s x) (@lem3353995 _87226 s x t h1)). Qed.
Lemma lem3354084 {_87226 : Type'} (_34976 : _87226 -> Prop) (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term279 _87226 s x _34976.
Proof. exact (@lem3354024 _87226 t s x h1 _34976). Qed.
Lemma lem3354085 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34976 : _87226 -> Prop) : (term279 _87226 s x _34976) = (term93 _87226 s x _34976).
Proof. exact (eq_refl (term279 _87226 s x _34976)). Qed.
Lemma lem3354087 {_87226 : Type'} (_34977 : _87226) (h1 : term53 _87226) : term280 _87226 _34977.
Proof. exact (@lem3354043 _87226 h1 _34977). Qed.
Lemma lem3354088 {_87226 : Type'} (_34977 : _87226) : (term280 _87226 _34977) = (term67 _87226 _34977).
Proof. exact (eq_refl (term280 _87226 _34977)). Qed.
Lemma lem3354093 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term281 _87226 s x _34979.
Proof. exact (@lem3354069 _87226 s x t h1 _34979). Qed.
Lemma lem3354094 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term281 _87226 s x _34979) = (term81 _87226 s x _34979).
Proof. exact (eq_refl (term281 _87226 s x _34979)). Qed.
Lemma lem3354095 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term81 _87226 s x _34979.
Proof. exact (EQ_MP (@lem3354094 _87226 s x _34979) (@lem3354093 _87226 _34979 s x t h1)). Qed.
Lemma lem3354105 {_87226 : Type'} (_34976 : _87226 -> Prop) (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term93 _87226 s x _34976.
Proof. exact (EQ_MP (@lem3354085 _87226 s x _34976) (@lem3354084 _87226 _34976 t s x h1)). Qed.
Lemma lem3354113 {_87226 : Type'} (_34977 : _87226) (h1 : term53 _87226) : term67 _87226 _34977.
Proof. exact (EQ_MP (@lem3354088 _87226 _34977) (@lem3354087 _87226 _34977 h1)). Qed.
Lemma lem3354126 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term81 _87226 s x _34979) = (term282 _87226 s x _34979).
Proof. exact (@lem3352576 (term283 _87226 _34979 s) (_34979 = (@EMPTY _87226)) (term77 _87226 x _34979)). Qed.
Lemma lem3354127 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term282 _87226 s x _34979.
Proof. exact (EQ_MP (@lem3354126 _87226 s x _34979) (@lem3354095 _87226 _34979 s x t h1)). Qed.
Lemma lem3354177 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : @IN (_87226 -> Prop) t s.
Proof. exact (proj1 (@lem3353991 _87226 t s x h1)). Qed.
Lemma lem3354178 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term284 _87226 t s.
Proof. exact (fun h0 : term283 _87226 t s => @lem3354177 _87226 t s x h1). Qed.
Lemma lem3354180 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354181 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) : (term284 _87226 t s) = (@IN (_87226 -> Prop) t s).
Proof. exact (@lem3354180 (@IN (_87226 -> Prop) t s)). Qed.
Lemma lem3354182 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : @IN (_87226 -> Prop) t s.
Proof. exact (EQ_MP (@lem3354181 _87226 t s) (@lem3354178 _87226 t s x h1)). Qed.
Lemma lem3354184 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : @IN _87226 x t.
Proof. exact (proj2 (@lem3353989 _87226 t s x h1)). Qed.
Lemma lem3354185 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term286 _87226 x t.
Proof. exact (fun h0 : term77 _87226 x t => @lem3354184 _87226 t s x h1). Qed.
Lemma lem3354187 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354188 {_87226 : Type'} (x : _87226) (t : _87226 -> Prop) : (term286 _87226 x t) = (@IN _87226 x t).
Proof. exact (@lem3354187 (@IN _87226 x t)). Qed.
Lemma lem3354189 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : @IN _87226 x t.
Proof. exact (EQ_MP (@lem3354188 _87226 x t) (@lem3354185 _87226 t s x h1)). Qed.
Lemma lem3354191 (a : Prop) (b : Prop) : (term287 a b) = (term288 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3354192 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34976 : _87226 -> Prop) : (term93 _87226 s x _34976) = (term92 _87226 s x _34976).
Proof. exact (@lem3354191 (@IN (_87226 -> Prop) _34976 s) (@IN _87226 x _34976)). Qed.
Lemma lem3354194 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3354195 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34976 : _87226 -> Prop) : (term92 _87226 s x _34976) = (term289 _87226 s x _34976).
Proof. exact (@lem3354194 (term69 _87226 s x _34976)). Qed.
Lemma lem3354196 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34976 : _87226 -> Prop) : (term93 _87226 s x _34976) = (term289 _87226 s x _34976).
Proof. exact (TRANS (@lem3354192 _87226 s x _34976) (@lem3354195 _87226 s x _34976)). Qed.
Lemma lem3354198 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term69 _87226 s x t.
Proof. exact (conj (@lem3354182 _87226 t s x h1) (@lem3354189 _87226 t s x h1)). Qed.
Lemma lem3354200 {_87226 : Type'} (_34976 : _87226 -> Prop) (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term289 _87226 s x _34976.
Proof. exact (EQ_MP (@lem3354196 _87226 s x _34976) (@lem3354105 _87226 _34976 t s x h1)). Qed.
Lemma lem3354201 {_87226 : Type'} (_34976 : _87226 -> Prop) (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term289 _87226 s x _34976.
Proof. exact (@lem3354200 _87226 _34976 t s x h1). Qed.
Lemma lem3354202 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term289 _87226 s x t.
Proof. exact (@lem3354201 _87226 t t s x h1). Qed.
Lemma lem3354205 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : False.
Proof. exact (@lem3354202 _87226 t s x h1 (@lem3354198 _87226 t s x h1)). Qed.
Lemma lem3354206 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : term290.
Proof. exact (fun h0 : ~ False => @lem3354205 _87226 t s x h1). Qed.
Lemma lem3354208 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354209 : term290 = False.
Proof. exact (@lem3354208 False). Qed.
Lemma lem3354210 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) (x : _87226) (h1 : term190 _87226 t s x) : False.
Proof. exact (EQ_MP (@lem3354209) (@lem3354206 _87226 t s x h1)). Qed.
Lemma lem3354230 {_87226 : Type'} : (@IN _87226) = (@IN _87226).
Proof. exact (eq_refl (@IN _87226)). Qed.
Lemma lem3354231 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) (h1 : _34992 = _34994) : _34992 = _34994.
Proof. exact (h1). Qed.
Lemma lem3354232 {_87226 : Type'} (_34993 : _87226 -> Prop) (_34995 : _87226 -> Prop) (h1 : _34993 = _34995) : _34993 = _34995.
Proof. exact (h1). Qed.
Lemma lem3354233 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) (h1 : _34992 = _34994) : (@IN _87226 _34992) = (@IN _87226 _34994).
Proof. exact (MK_COMB (@lem3354230 _87226) (@lem3354231 _87226 _34992 _34994 h1)). Qed.
Lemma lem3354234 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) (_34993 : _87226 -> Prop) (_34995 : _87226 -> Prop) (h1 : _34992 = _34994) (h2 : _34993 = _34995) : (@IN _87226 _34992 _34993) = (@IN _87226 _34994 _34995).
Proof. exact (MK_COMB (@lem3354233 _87226 _34992 _34994 h1) (@lem3354232 _87226 _34993 _34995 h2)). Qed.
Lemma lem3354236 (b : Prop) (a : Prop) : term291 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3354237 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : term292 _87226 _34994 _34995 _34992 _34993.
Proof. exact (@lem3354236 (@IN _87226 _34994 _34995) (@IN _87226 _34992 _34993)). Qed.
Lemma lem3354238 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) (_34993 : _87226 -> Prop) (_34995 : _87226 -> Prop) (h1 : _34992 = _34994) (h2 : _34993 = _34995) : term293 _87226 _34994 _34995 _34992 _34993.
Proof. exact (@lem3354237 _87226 _34994 _34995 _34992 _34993 (@lem3354234 _87226 _34992 _34994 _34993 _34995 h1 h2)). Qed.
Lemma lem3354239 {_87226 : Type'} (_34995 : _87226 -> Prop) (_34993 : _87226 -> Prop) (_34992 : _87226) (_34994 : _87226) (h1 : _34992 = _34994) : term294 _87226 _34994 _34995 _34992 _34993.
Proof. exact (fun h0 : _34993 = _34995 => @lem3354238 _87226 _34992 _34994 _34993 _34995 h1 h0). Qed.
Lemma lem3354241 (a : Prop) (b : Prop) : (a -> b) = (term295 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3354242 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term294 _87226 _34994 _34995 _34992 _34993) = (term296 _87226 _34994 _34995 _34992 _34993).
Proof. exact (@lem3354241 (_34993 = _34995) (term293 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354243 {_87226 : Type'} (_34995 : _87226 -> Prop) (_34993 : _87226 -> Prop) (_34992 : _87226) (_34994 : _87226) (h1 : _34992 = _34994) : term296 _87226 _34994 _34995 _34992 _34993.
Proof. exact (EQ_MP (@lem3354242 _87226 _34994 _34995 _34992 _34993) (@lem3354239 _87226 _34995 _34993 _34992 _34994 h1)). Qed.
Lemma lem3354244 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : term297 _87226 _34994 _34995 _34992 _34993.
Proof. exact (fun h0 : _34992 = _34994 => @lem3354243 _87226 _34995 _34993 _34992 _34994 h0). Qed.
Lemma lem3354246 (a : Prop) (b : Prop) : (a -> b) = (term295 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3354247 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term297 _87226 _34994 _34995 _34992 _34993) = (term298 _87226 _34994 _34995 _34992 _34993).
Proof. exact (@lem3354246 (_34992 = _34994) (term296 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354248 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : term298 _87226 _34994 _34995 _34992 _34993.
Proof. exact (EQ_MP (@lem3354247 _87226 _34994 _34995 _34992 _34993) (@lem3354244 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354256 {_87226 : Type'} (x : _87226) : x = x.
Proof. exact (@lem21386 _87226 x). Qed.
Lemma lem3354257 {_87226 : Type'} (x : _87226) : x = x.
Proof. exact (@lem3354256 _87226 x). Qed.
Lemma lem3354258 {_87226 : Type'} (x : _87226) : term299 _87226 x.
Proof. exact (fun h0 : term300 _87226 x => @lem3354257 _87226 x). Qed.
Lemma lem3354260 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354261 {_87226 : Type'} (x : _87226) : (term299 _87226 x) = (x = x).
Proof. exact (@lem3354260 (x = x)). Qed.
Lemma lem3354262 {_87226 : Type'} (x : _87226) : x = x.
Proof. exact (EQ_MP (@lem3354261 _87226 x) (@lem3354258 _87226 x)). Qed.
Lemma lem3354264 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN (_87226 -> Prop) t s.
Proof. exact (proj1 (@lem3353994 _87226 s x t h1)). Qed.
Lemma lem3354265 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term284 _87226 t s.
Proof. exact (fun h0 : term283 _87226 t s => @lem3354264 _87226 s x t h1). Qed.
Lemma lem3354267 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354268 {_87226 : Type'} (t : _87226 -> Prop) (s : type686 _87226) : (term284 _87226 t s) = (@IN (_87226 -> Prop) t s).
Proof. exact (@lem3354267 (@IN (_87226 -> Prop) t s)). Qed.
Lemma lem3354269 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN (_87226 -> Prop) t s.
Proof. exact (EQ_MP (@lem3354268 _87226 t s) (@lem3354265 _87226 s x t h1)). Qed.
Lemma lem3354271 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x t.
Proof. exact (proj2 (@lem3353994 _87226 s x t h1)). Qed.
Lemma lem3354272 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term286 _87226 x t.
Proof. exact (fun h0 : term77 _87226 x t => @lem3354271 _87226 s x t h1). Qed.
Lemma lem3354274 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354275 {_87226 : Type'} (x : _87226) (t : _87226 -> Prop) : (term286 _87226 x t) = (@IN _87226 x t).
Proof. exact (@lem3354274 (@IN _87226 x t)). Qed.
Lemma lem3354276 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x t.
Proof. exact (EQ_MP (@lem3354275 _87226 x t) (@lem3354272 _87226 s x t h1)). Qed.
Lemma lem3354282 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3354283 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term282 _87226 s x _34979) = (term301 _87226 s x _34979).
Proof. exact (@lem3354282 (_34979 = (@EMPTY _87226)) (term283 _87226 _34979 s) (term77 _87226 x _34979)). Qed.
Lemma lem3354299 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3354300 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term93 _87226 s x _34979) = (term302 _87226 x _34979 s).
Proof. exact (@lem3354299 (term77 _87226 x _34979) (term283 _87226 _34979 s)). Qed.
Lemma lem3354306 {_87226 : Type'} (_34979 : _87226 -> Prop) : (term303 _87226 _34979) = (term303 _87226 _34979).
Proof. exact (eq_refl (term303 _87226 _34979)). Qed.
Lemma lem3354307 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term301 _87226 s x _34979) = (term304 _87226 x _34979 s).
Proof. exact (MK_COMB (@lem3354306 _87226 _34979) (@lem3354300 _87226 x _34979 s)). Qed.
Lemma lem3354318 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term282 _87226 s x _34979) = (term304 _87226 x _34979 s).
Proof. exact (TRANS (@lem3354283 _87226 s x _34979) (@lem3354307 _87226 x _34979 s)). Qed.
Lemma lem3354319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3354320 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term305 _87226 s x _34979) = (term306 _87226 x _34979 s).
Proof. exact (MK_COMB (@lem3354319) (@lem3354318 _87226 x _34979 s)). Qed.
Lemma lem3354336 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3354337 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term93 _87226 s x _34979) = (term302 _87226 x _34979 s).
Proof. exact (@lem3354336 (term77 _87226 x _34979) (term283 _87226 _34979 s)). Qed.
Lemma lem3354343 {_87226 : Type'} (_34979 : _87226 -> Prop) : (term303 _87226 _34979) = (term303 _87226 _34979).
Proof. exact (eq_refl (term303 _87226 _34979)). Qed.
Lemma lem3354344 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : (term301 _87226 s x _34979) = (term304 _87226 x _34979 s).
Proof. exact (MK_COMB (@lem3354343 _87226 _34979) (@lem3354337 _87226 x _34979 s)). Qed.
Lemma lem3354355 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : ((term282 _87226 s x _34979) = (term301 _87226 s x _34979)) = ((term304 _87226 x _34979 s) = (term304 _87226 x _34979 s)).
Proof. exact (MK_COMB (@lem3354320 _87226 x _34979 s) (@lem3354344 _87226 x _34979 s)). Qed.
Lemma lem3354357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3354358 (x : Prop) : (x = x) = True.
Proof. exact (@lem3354357 Prop x). Qed.
Lemma lem3354359 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) (s : type686 _87226) : ((term304 _87226 x _34979 s) = (term304 _87226 x _34979 s)) = True.
Proof. exact (@lem3354358 (term304 _87226 x _34979 s)). Qed.
Lemma lem3354360 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : ((term282 _87226 s x _34979) = (term301 _87226 s x _34979)) = True.
Proof. exact (TRANS (@lem3354355 _87226 x _34979 s) (@lem3354359 _87226 x _34979 s)). Qed.
Lemma lem3354361 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : True = ((term282 _87226 s x _34979) = (term301 _87226 s x _34979)).
Proof. exact (SYM (@lem3354360 _87226 s x _34979)). Qed.
Lemma lem3354362 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term282 _87226 s x _34979) = (term301 _87226 s x _34979).
Proof. exact (EQ_MP (@lem3354361 _87226 s x _34979) (@lem0)). Qed.
Lemma lem3354363 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term301 _87226 s x _34979.
Proof. exact (EQ_MP (@lem3354362 _87226 s x _34979) (@lem3354127 _87226 _34979 s x t h1)). Qed.
Lemma lem3354365 (b : Prop) (a : Prop) : (a \/ b) = (term307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3354366 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term301 _87226 s x _34979) = (term308 _87226 s x _34979).
Proof. exact (@lem3354365 (term93 _87226 s x _34979) (_34979 = (@EMPTY _87226))). Qed.
Lemma lem3354368 (a : Prop) (b : Prop) : (term309 a b) = (term310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3354369 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term311 _87226 s x _34979) = (term312 _87226 s x _34979).
Proof. exact (@lem3354368 (term283 _87226 _34979 s) (term77 _87226 x _34979)). Qed.
Lemma lem3354371 (a : Prop) : (term313 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3354372 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) : (term314 _87226 _34979 s) = (@IN (_87226 -> Prop) _34979 s).
Proof. exact (@lem3354371 (@IN (_87226 -> Prop) _34979 s)). Qed.
Lemma lem3354373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3354374 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) : (term315 _87226 _34979 s) = (term316 _87226 _34979 s).
Proof. exact (MK_COMB (@lem3354373) (@lem3354372 _87226 _34979 s)). Qed.
Lemma lem3354376 (a : Prop) : (term313 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3354377 {_87226 : Type'} (x : _87226) (_34979 : _87226 -> Prop) : (term317 _87226 x _34979) = (@IN _87226 x _34979).
Proof. exact (@lem3354376 (@IN _87226 x _34979)). Qed.
Lemma lem3354378 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term312 _87226 s x _34979) = (term69 _87226 s x _34979).
Proof. exact (MK_COMB (@lem3354374 _87226 _34979 s) (@lem3354377 _87226 x _34979)). Qed.
Lemma lem3354379 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term311 _87226 s x _34979) = (term69 _87226 s x _34979).
Proof. exact (TRANS (@lem3354369 _87226 s x _34979) (@lem3354378 _87226 s x _34979)). Qed.
Lemma lem3354380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3354381 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term318 _87226 s x _34979) = (term319 _87226 s x _34979).
Proof. exact (MK_COMB (@lem3354380) (@lem3354379 _87226 s x _34979)). Qed.
Lemma lem3354382 {_87226 : Type'} (_34979 : _87226 -> Prop) : (_34979 = (@EMPTY _87226)) = (_34979 = (@EMPTY _87226)).
Proof. exact (eq_refl (_34979 = (@EMPTY _87226))). Qed.
Lemma lem3354383 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term308 _87226 s x _34979) = (term320 _87226 s x _34979).
Proof. exact (MK_COMB (@lem3354381 _87226 s x _34979) (@lem3354382 _87226 _34979)). Qed.
Lemma lem3354384 {_87226 : Type'} (s : type686 _87226) (x : _87226) (_34979 : _87226 -> Prop) : (term301 _87226 s x _34979) = (term320 _87226 s x _34979).
Proof. exact (TRANS (@lem3354366 _87226 s x _34979) (@lem3354383 _87226 s x _34979)). Qed.
Lemma lem3354386 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term69 _87226 s x t.
Proof. exact (conj (@lem3354269 _87226 s x t h1) (@lem3354276 _87226 s x t h1)). Qed.
Lemma lem3354388 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term320 _87226 s x _34979.
Proof. exact (EQ_MP (@lem3354384 _87226 s x _34979) (@lem3354363 _87226 _34979 s x t h1)). Qed.
Lemma lem3354389 {_87226 : Type'} (_34979 : _87226 -> Prop) (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term320 _87226 s x _34979.
Proof. exact (@lem3354388 _87226 _34979 s x t h1). Qed.
Lemma lem3354390 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term320 _87226 s x t.
Proof. exact (@lem3354389 _87226 t s x t h1). Qed.
Lemma lem3354393 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : t = (@EMPTY _87226).
Proof. exact (@lem3354390 _87226 s x t h1 (@lem3354386 _87226 s x t h1)). Qed.
Lemma lem3354394 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term321 _87226 t.
Proof. exact (fun h0 : term76 _87226 t => @lem3354393 _87226 s x t h1). Qed.
Lemma lem3354396 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354397 {_87226 : Type'} (t : _87226 -> Prop) : (term321 _87226 t) = (t = (@EMPTY _87226)).
Proof. exact (@lem3354396 (t = (@EMPTY _87226))). Qed.
Lemma lem3354398 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : t = (@EMPTY _87226).
Proof. exact (EQ_MP (@lem3354397 _87226 t) (@lem3354394 _87226 s x t h1)). Qed.
Lemma lem3354400 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x t.
Proof. exact (proj2 (@lem3353994 _87226 s x t h1)). Qed.
Lemma lem3354401 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term286 _87226 x t.
Proof. exact (fun h0 : term77 _87226 x t => @lem3354400 _87226 s x t h1). Qed.
Lemma lem3354403 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354404 {_87226 : Type'} (x : _87226) (t : _87226 -> Prop) : (term286 _87226 x t) = (@IN _87226 x t).
Proof. exact (@lem3354403 (@IN _87226 x t)). Qed.
Lemma lem3354405 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x t.
Proof. exact (EQ_MP (@lem3354404 _87226 x t) (@lem3354401 _87226 s x t h1)). Qed.
Lemma lem3354423 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3354424 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term296 _87226 _34994 _34995 _34992 _34993) = (term322 _87226 _34994 _34995 _34992 _34993).
Proof. exact (@lem3354423 (@IN _87226 _34994 _34995) (term323 _87226 _34993 _34995) (term77 _87226 _34992 _34993)). Qed.
Lemma lem3354442 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) : (term324 _87226 _34992 _34994) = (term324 _87226 _34992 _34994).
Proof. exact (eq_refl (term324 _87226 _34992 _34994)). Qed.
Lemma lem3354443 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term298 _87226 _34994 _34995 _34992 _34993) = (term325 _87226 _34994 _34995 _34992 _34993).
Proof. exact (MK_COMB (@lem3354442 _87226 _34992 _34994) (@lem3354424 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354447 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3354448 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term325 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993).
Proof. exact (@lem3354447 (@IN _87226 _34994 _34995) (term327 _87226 _34992 _34994) (term328 _87226 _34995 _34992 _34993)). Qed.
Lemma lem3354478 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term298 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993).
Proof. exact (TRANS (@lem3354443 _87226 _34994 _34995 _34992 _34993) (@lem3354448 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3354480 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term329 _87226 _34994 _34995 _34992 _34993) = (term330 _87226 _34994 _34995 _34992 _34993).
Proof. exact (MK_COMB (@lem3354479) (@lem3354478 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354510 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term326 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993).
Proof. exact (eq_refl (term326 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354511 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : ((term298 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993)) = ((term326 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993)).
Proof. exact (MK_COMB (@lem3354480 _87226 _34994 _34995 _34992 _34993) (@lem3354510 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3354514 (x : Prop) : (x = x) = True.
Proof. exact (@lem3354513 Prop x). Qed.
Lemma lem3354515 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : ((term326 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993)) = True.
Proof. exact (@lem3354514 (term326 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354516 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : ((term298 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993)) = True.
Proof. exact (TRANS (@lem3354511 _87226 _34994 _34995 _34992 _34993) (@lem3354515 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354517 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : True = ((term298 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993)).
Proof. exact (SYM (@lem3354516 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354518 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term298 _87226 _34994 _34995 _34992 _34993) = (term326 _87226 _34994 _34995 _34992 _34993).
Proof. exact (EQ_MP (@lem3354517 _87226 _34994 _34995 _34992 _34993) (@lem0)). Qed.
Lemma lem3354519 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : term326 _87226 _34994 _34995 _34992 _34993.
Proof. exact (EQ_MP (@lem3354518 _87226 _34994 _34995 _34992 _34993) (@lem3354248 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354521 (b : Prop) (a : Prop) : (a \/ b) = (term307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3354522 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) (_34994 : _87226) (_34995 : _87226 -> Prop) : (term326 _87226 _34994 _34995 _34992 _34993) = (term331 _87226 _34992 _34993 _34994 _34995).
Proof. exact (@lem3354521 (term332 _87226 _34994 _34995 _34992 _34993) (@IN _87226 _34994 _34995)). Qed.
Lemma lem3354524 (a : Prop) (b : Prop) : (term309 a b) = (term310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3354525 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term333 _87226 _34994 _34995 _34992 _34993) = (term334 _87226 _34994 _34995 _34992 _34993).
Proof. exact (@lem3354524 (term327 _87226 _34992 _34994) (term328 _87226 _34995 _34992 _34993)). Qed.
Lemma lem3354527 (a : Prop) : (term313 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3354528 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) : (term335 _87226 _34992 _34994) = (_34992 = _34994).
Proof. exact (@lem3354527 (_34992 = _34994)). Qed.
Lemma lem3354529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3354530 {_87226 : Type'} (_34992 : _87226) (_34994 : _87226) : (term336 _87226 _34992 _34994) = (term337 _87226 _34992 _34994).
Proof. exact (MK_COMB (@lem3354529) (@lem3354528 _87226 _34992 _34994)). Qed.
Lemma lem3354532 (a : Prop) (b : Prop) : (term309 a b) = (term310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3354533 {_87226 : Type'} (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term338 _87226 _34995 _34992 _34993) = (term339 _87226 _34995 _34992 _34993).
Proof. exact (@lem3354532 (term323 _87226 _34993 _34995) (term77 _87226 _34992 _34993)). Qed.
Lemma lem3354535 (a : Prop) : (term313 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3354536 {_87226 : Type'} (_34993 : _87226 -> Prop) (_34995 : _87226 -> Prop) : (term340 _87226 _34993 _34995) = (_34993 = _34995).
Proof. exact (@lem3354535 (_34993 = _34995)). Qed.
Lemma lem3354537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3354538 {_87226 : Type'} (_34993 : _87226 -> Prop) (_34995 : _87226 -> Prop) : (term341 _87226 _34993 _34995) = (term342 _87226 _34993 _34995).
Proof. exact (MK_COMB (@lem3354537) (@lem3354536 _87226 _34993 _34995)). Qed.
Lemma lem3354540 (a : Prop) : (term313 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3354541 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) : (term317 _87226 _34992 _34993) = (@IN _87226 _34992 _34993).
Proof. exact (@lem3354540 (@IN _87226 _34992 _34993)). Qed.
Lemma lem3354542 {_87226 : Type'} (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term339 _87226 _34995 _34992 _34993) = (term343 _87226 _34995 _34992 _34993).
Proof. exact (MK_COMB (@lem3354538 _87226 _34993 _34995) (@lem3354541 _87226 _34992 _34993)). Qed.
Lemma lem3354543 {_87226 : Type'} (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term338 _87226 _34995 _34992 _34993) = (term343 _87226 _34995 _34992 _34993).
Proof. exact (TRANS (@lem3354533 _87226 _34995 _34992 _34993) (@lem3354542 _87226 _34995 _34992 _34993)). Qed.
Lemma lem3354544 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term334 _87226 _34994 _34995 _34992 _34993) = (term344 _87226 _34994 _34995 _34992 _34993).
Proof. exact (MK_COMB (@lem3354530 _87226 _34992 _34994) (@lem3354543 _87226 _34995 _34992 _34993)). Qed.
Lemma lem3354545 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term333 _87226 _34994 _34995 _34992 _34993) = (term344 _87226 _34994 _34995 _34992 _34993).
Proof. exact (TRANS (@lem3354525 _87226 _34994 _34995 _34992 _34993) (@lem3354544 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3354547 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) (_34992 : _87226) (_34993 : _87226 -> Prop) : (term345 _87226 _34994 _34995 _34992 _34993) = (term346 _87226 _34994 _34995 _34992 _34993).
Proof. exact (MK_COMB (@lem3354546) (@lem3354545 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354548 {_87226 : Type'} (_34994 : _87226) (_34995 : _87226 -> Prop) : (@IN _87226 _34994 _34995) = (@IN _87226 _34994 _34995).
Proof. exact (eq_refl (@IN _87226 _34994 _34995)). Qed.
Lemma lem3354549 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) (_34994 : _87226) (_34995 : _87226 -> Prop) : (term331 _87226 _34992 _34993 _34994 _34995) = (term347 _87226 _34992 _34993 _34994 _34995).
Proof. exact (MK_COMB (@lem3354547 _87226 _34994 _34995 _34992 _34993) (@lem3354548 _87226 _34994 _34995)). Qed.
Lemma lem3354550 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) (_34994 : _87226) (_34995 : _87226 -> Prop) : (term326 _87226 _34994 _34995 _34992 _34993) = (term347 _87226 _34992 _34993 _34994 _34995).
Proof. exact (TRANS (@lem3354522 _87226 _34992 _34993 _34994 _34995) (@lem3354549 _87226 _34992 _34993 _34994 _34995)). Qed.
Lemma lem3354552 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term348 _87226 x t.
Proof. exact (conj (@lem3354398 _87226 s x t h1) (@lem3354405 _87226 s x t h1)). Qed.
Lemma lem3354553 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term349 _87226 x t.
Proof. exact (conj (@lem3354262 _87226 x) (@lem3354552 _87226 s x t h1)). Qed.
Lemma lem3354555 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) (_34994 : _87226) (_34995 : _87226 -> Prop) : term347 _87226 _34992 _34993 _34994 _34995.
Proof. exact (EQ_MP (@lem3354550 _87226 _34992 _34993 _34994 _34995) (@lem3354519 _87226 _34994 _34995 _34992 _34993)). Qed.
Lemma lem3354556 {_87226 : Type'} (_34992 : _87226) (_34993 : _87226 -> Prop) (_34994 : _87226) (_34995 : _87226 -> Prop) : term347 _87226 _34992 _34993 _34994 _34995.
Proof. exact (@lem3354555 _87226 _34992 _34993 _34994 _34995). Qed.
Lemma lem3354557 {_87226 : Type'} (t : _87226 -> Prop) (x : _87226) : term350 _87226 t x.
Proof. exact (@lem3354556 _87226 x t x (@EMPTY _87226)). Qed.
Lemma lem3354560 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x (@EMPTY _87226).
Proof. exact (@lem3354557 _87226 t x (@lem3354553 _87226 s x t h1)). Qed.
Lemma lem3354561 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : term351 _87226 x.
Proof. exact (fun h0 : term67 _87226 x => @lem3354560 _87226 s x t h1). Qed.
Lemma lem3354563 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354564 {_87226 : Type'} (x : _87226) : (term351 _87226 x) = (@IN _87226 x (@EMPTY _87226)).
Proof. exact (@lem3354563 (@IN _87226 x (@EMPTY _87226))). Qed.
Lemma lem3354565 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term210 _87226 s x t) : @IN _87226 x (@EMPTY _87226).
Proof. exact (EQ_MP (@lem3354564 _87226 x) (@lem3354561 _87226 s x t h1)). Qed.
Lemma lem3354568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3354570 {_87226 : Type'} (_34977 : _87226) : (term67 _87226 _34977) = (term352 _87226 _34977).
Proof. exact (@lem3354568 (@IN _87226 _34977 (@EMPTY _87226))). Qed.
Lemma lem3354573 {_87226 : Type'} (_34977 : _87226) (h1 : term53 _87226) : term352 _87226 _34977.
Proof. exact (EQ_MP (@lem3354570 _87226 _34977) (@lem3354113 _87226 _34977 h1)). Qed.
Lemma lem3354574 {_87226 : Type'} (_34977 : _87226) (h1 : term53 _87226) : term352 _87226 _34977.
Proof. exact (@lem3354573 _87226 _34977 h1). Qed.
Lemma lem3354575 {_87226 : Type'} (x : _87226) (h1 : term53 _87226) : term352 _87226 x.
Proof. exact (@lem3354574 _87226 x h1). Qed.
Lemma lem3354578 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term210 _87226 s x t) : False.
Proof. exact (@lem3354575 _87226 x h1 (@lem3354565 _87226 s x t h2)). Qed.
Lemma lem3354579 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term210 _87226 s x t) : term290.
Proof. exact (fun h0 : ~ False => @lem3354578 _87226 s x t h1 h2). Qed.
Lemma lem3354581 (p : Prop) : (term285 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3354582 : term290 = False.
Proof. exact (@lem3354581 False). Qed.
Lemma lem3354583 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term210 _87226 s x t) : False.
Proof. exact (EQ_MP (@lem3354582) (@lem3354579 _87226 s x t h1 h2)). Qed.
Lemma lem3354584 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term210 _87226 s x t) : (term53 _87226) = False.
Proof. exact (prop_ext (fun h3 : term53 _87226 => @lem3354583 _87226 s x t h1 h2) (fun h3 : False => @lem3354043 _87226 h1)). Qed.
Lemma lem3354585 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term210 _87226 s x t) : False.
Proof. exact (EQ_MP (@lem3354584 _87226 s x t h1 h2) (@lem3354043 _87226 h1)). Qed.
Lemma lem3354586 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term271 _87226 s x t) : False.
Proof. exact (or_elim (@lem3353985 _87226 s x t h2) (fun h0 : term190 _87226 t s x => @lem3354210 _87226 t s x h0) (fun h0 : term210 _87226 s x t => @lem3354585 _87226 s x t h1 h0)). Qed.
Lemma lem3354587 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term271 _87226 s x t) : (term271 _87226 s x t) = False.
Proof. exact (prop_ext (fun h3 : term271 _87226 s x t => @lem3354586 _87226 s x t h1 h2) (fun h3 : False => @lem3353985 _87226 s x t h2)). Qed.
Lemma lem3354588 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term271 _87226 s x t) : False.
Proof. exact (EQ_MP (@lem3354587 _87226 s x t h1 h2) (@lem3353985 _87226 s x t h2)). Qed.
Lemma lem3354589 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term271 _87226 s x t) : (term53 _87226) = False.
Proof. exact (prop_ext (fun h3 : term53 _87226 => @lem3354588 _87226 s x t h1 h2) (fun h3 : False => @lem3353880 _87226 h1)). Qed.
Lemma lem3354590 {_87226 : Type'} (s : type686 _87226) (x : _87226) (t : _87226 -> Prop) (h1 : term53 _87226) (h2 : term271 _87226 s x t) : False.
Proof. exact (EQ_MP (@lem3354589 _87226 s x t h1 h2) (@lem3353880 _87226 h1)). Qed.
Lemma lem3354591 {_87226 : Type'} (s : type686 _87226) (x : _87226) (h1 : term53 _87226) (h2 : term274 _87226 s x) : False.
Proof. exact (ex_elim (@lem3353868 _87226 s x h2) (fun t : _87226 -> Prop => fun h0 : term273 _87226 s x t => @lem3354590 _87226 s x t h1 h0)). Qed.
Lemma lem3354592 {_87226 : Type'} (s : type686 _87226) (h1 : term53 _87226) (h2 : term276 _87226 s) : False.
Proof. exact (ex_elim (@lem3353867 _87226 s h2) (fun x : _87226 => fun h0 : term275 _87226 s x => @lem3354591 _87226 s x h1 h0)). Qed.
Lemma lem3354593 {_87226 : Type'} (h1 : term53 _87226) (h2 : term51 _87226) : False.
Proof. exact (ex_elim (@lem3353840 _87226 h2) (fun s : type686 _87226 => fun h0 : term277 _87226 s => @lem3354592 _87226 s h1 h0)). Qed.
Lemma lem3354594 {_87226 : Type'} (h1 : term53 _87226) (h2 : term51 _87226) : (term53 _87226) = False.
Proof. exact (prop_ext (fun h3 : term53 _87226 => @lem3354593 _87226 h1 h2) (fun h3 : False => @lem3353853 _87226 h1)). Qed.
Lemma lem3354595 {_87226 : Type'} (h1 : term53 _87226) (h2 : term51 _87226) : False.
Proof. exact (EQ_MP (@lem3354594 _87226 h1 h2) (@lem3353853 _87226 h1)). Qed.
Lemma lem3354596 {_87226 : Type'} (h1 : term53 _87226) (h2 : term51 _87226) : term58 _87226.
Proof. exact (fun h0 : term52 _87226 => @lem3354595 _87226 h1 h2). Qed.
Lemma lem3354597 {_87226 : Type'} : (term58 _87226) = (term59 _87226).
Proof. exact (@lem69 (term52 _87226)). Qed.
Lemma lem3354598 {_87226 : Type'} (h1 : term53 _87226) (h2 : term51 _87226) : term59 _87226.
Proof. exact (EQ_MP (@lem3354597 _87226) (@lem3354596 _87226 h1 h2)). Qed.
Lemma lem3354599 {_87226 : Type'} (h1 : term51 _87226) : term62 _87226.
Proof. exact (fun h0 : term53 _87226 => @lem3354598 _87226 h0 h1). Qed.
Lemma lem3354600 {_87226 : Type'} : term64 _87226.
Proof. exact (fun h0 : term51 _87226 => @lem3354599 _87226 h0). Qed.
Lemma lem3354601 {_87226 : Type'} : term54 _87226.
Proof. exact (EQ_MP (@lem3352946 _87226) (@lem3354600 _87226)). Qed.
Lemma lem3354603 {_87226 : Type'} : term54 _87226.
Proof. exact (@lem3352706 _87226 (@lem3354601 _87226)). Qed.
Lemma lem3354604 {_87226 : Type'} (h1 : term51 _87226) : term61 _87226.
Proof. exact (@lem3354603 _87226 (@lem3352687 _87226 h1)). Qed.
Lemma lem3354605 {_87226 : Type'} (h1 : term51 _87226) : term58 _87226.
Proof. exact (@lem3354604 _87226 h1 (@lem3352689 _87226)). Qed.
Lemma lem3354606 {_87226 : Type'} (h1 : term51 _87226) : False.
Proof. exact (@lem3354605 _87226 h1 (@lem3352688 _87226)). Qed.
Lemma lem3354607 {_87226 : Type'} (h1 : term51 _87226) : (term51 _87226) = False.
Proof. exact (prop_ext (fun h2 : term51 _87226 => @lem3354606 _87226 h1) (fun h2 : False => @lem3352687 _87226 h1)). Qed.
Lemma lem3354608 {_87226 : Type'} (h1 : term51 _87226) : False.
Proof. exact (EQ_MP (@lem3354607 _87226 h1) (@lem3352687 _87226 h1)). Qed.
Lemma lem3354609 {_87226 : Type'} : term50 _87226.
Proof. exact (fun h0 : term51 _87226 => @lem3354608 _87226 h0). Qed.
Lemma lem3354610 {_87226 : Type'} : term48 _87226.
Proof. exact (EQ_MP (@lem3352686 _87226) (@lem3354609 _87226)). Qed.
Lemma lem3354611 {_87226 : Type'} : term28 _87226.
Proof. exact (EQ_MP (@lem3352682 _87226) (@lem3354610 _87226)). Qed.
Lemma lem3354612 {_87226 : Type'} : term27 _87226.
Proof. exact (EQ_MP (@lem3352611 _87226) (@lem3354611 _87226)). Qed.
