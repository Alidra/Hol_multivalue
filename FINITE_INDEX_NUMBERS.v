Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDEX_NUMBERS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDEX_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5423179 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5423180 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5423181 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5423180 t1) (@lem5423179 t1)). Qed.
Lemma lem5423182 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5423181 t1 t2). Qed.
Lemma lem5423183 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5423184 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5423183 t1 t2) (@lem5423182 t1 t2)). Qed.
Lemma lem5423185 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5423184 t1 t2 t3). Qed.
Lemma lem5423186 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5423187 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5423186 t1 t2 t3) (@lem5423185 t1 t2 t3)). Qed.
Lemma lem5423188 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5423187 t1 t2 t3)). Qed.
Lemma lem5423190 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5423191 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem5423190 (term8 A)). Qed.
Lemma lem5423192 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem5423191 A)). Qed.
Lemma lem5423193 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem5423194 {A : Type'} : term11 A.
Proof. exact (@lem5423178 A). Qed.
Lemma lem5423195 : term12.
Proof. exact (@lem5423178 nat). Qed.
Lemma lem5423198 {A : Type'} : term13 A.
Proof. exact (@lem5423178 (A -> Prop)). Qed.
Lemma lem5423201 {A B : Type'} : term14 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem5423202 {B : Type'} : term15 B.
Proof. exact (@lem3615104 nat B). Qed.
Lemma lem5423203 {A B : Type'} : term16 A B.
Proof. exact (@lem3615104 (A -> Prop) B). Qed.
Lemma lem5423204 {A : Type'} : term17 A.
Proof. exact (@lem3615104 A A). Qed.
Lemma lem5423205 {A : Type'} : term18 A.
Proof. exact (@lem3615104 A nat). Qed.
Lemma lem5423206 {A : Type'} : term19 A.
Proof. exact (@lem3615104 A (A -> Prop)). Qed.
Lemma lem5423207 {A : Type'} : term15 A.
Proof. exact (@lem3615104 nat A). Qed.
Lemma lem5423208 : term20.
Proof. exact (@lem3615104 nat nat). Qed.
Lemma lem5423209 {A : Type'} : term21 A.
Proof. exact (@lem3615104 nat (A -> Prop)). Qed.
Lemma lem5423212 {A B : Type'} (h1 : term22 A B) : term22 A B.
Proof. exact (h1). Qed.
Lemma lem5423213 {A B : Type'} : term23 A B.
Proof. exact (fun h0 : term22 A B => @lem5423212 A B h0). Qed.
Lemma lem5423214 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (h1). Qed.
Lemma lem5423215 {A B : Type'} (h1 : term22 A B) : term22 A B.
Proof. exact (h1). Qed.
Lemma lem5423216 {A B : Type'} (h1 : term22 A B) (h2 : term23 A B) : term22 A B.
Proof. exact (@lem5423214 A B h2 (@lem5423215 A B h1)). Qed.
Lemma lem5423217 {A B : Type'} (h1 : term22 A B) : term24 A B.
Proof. exact (fun h0 : term23 A B => @lem5423216 A B h1 h0). Qed.
Lemma lem5423218 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (h1). Qed.
Lemma lem5423219 {A B : Type'} (h1 : term22 A B) (h2 : term23 A B) : term22 A B.
Proof. exact (@lem5423217 A B h1 (@lem5423218 A B h2)). Qed.
Lemma lem5423220 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (fun h0 : term22 A B => @lem5423219 A B h0 h1). Qed.
Lemma lem5423221 {A B : Type'} : term25 A B.
Proof. exact (fun h0 : term23 A B => @lem5423220 A B h0). Qed.
Lemma lem5423224 {A B : Type'} : term23 A B.
Proof. exact (@lem5423221 A B (@lem5423213 A B)). Qed.
Lemma lem5423225 {A B : Type'} : term23 A B.
Proof. exact (@lem5423224 A B). Qed.
Lemma lem5423561 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5423562 : term26 = term27.
Proof. exact (@lem5423561 term12). Qed.
Lemma lem5423631 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem5423632 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (MK_COMB (@lem5423631 A) (@lem5423562)). Qed.
Lemma lem5423635 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (eq_refl (term31 A)). Qed.
Lemma lem5423636 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (MK_COMB (@lem5423635 A) (@lem5423632 A)). Qed.
Lemma lem5423639 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem5423640 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem5423639) (@lem5423636 A)). Qed.
Lemma lem5423643 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem5423644 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem5423643) (@lem5423640 A)). Qed.
Lemma lem5423647 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (eq_refl (term40 A)). Qed.
Lemma lem5423648 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (MK_COMB (@lem5423647 A) (@lem5423644 A)). Qed.
Lemma lem5423651 {B : Type'} : (term43 B) = (term43 B).
Proof. exact (eq_refl (term43 B)). Qed.
Lemma lem5423652 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem5423651 B) (@lem5423648 A)). Qed.
Lemma lem5423655 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (eq_refl (term43 A)). Qed.
Lemma lem5423656 {A B : Type'} : (term46 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem5423655 A) (@lem5423652 A B)). Qed.
Lemma lem5423659 {A B : Type'} : (term48 A B) = (term48 A B).
Proof. exact (eq_refl (term48 A B)). Qed.
Lemma lem5423660 {A B : Type'} : (term49 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem5423659 A B) (@lem5423656 A B)). Qed.
Lemma lem5423663 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (eq_refl (term51 A)). Qed.
Lemma lem5423664 {A B : Type'} : (term52 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem5423663 A) (@lem5423660 A B)). Qed.
Lemma lem5423667 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (eq_refl (term54 A)). Qed.
Lemma lem5423668 {A B : Type'} : (term55 A B) = (term56 A B).
Proof. exact (MK_COMB (@lem5423667 A) (@lem5423664 A B)). Qed.
Lemma lem5423671 {A B : Type'} : (term57 A B) = (term57 A B).
Proof. exact (eq_refl (term57 A B)). Qed.
Lemma lem5423672 {A B : Type'} : (term58 A B) = (term59 A B).
Proof. exact (MK_COMB (@lem5423671 A B) (@lem5423668 A B)). Qed.
Lemma lem5423675 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem5423676 {A B : Type'} : (term61 A B) = (term62 A B).
Proof. exact (MK_COMB (@lem5423675 A) (@lem5423672 A B)). Qed.
Lemma lem5423679 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (eq_refl (term63 A)). Qed.
Lemma lem5423686 {A B : Type'} : (term22 A B) = (term64 A B).
Proof. exact (MK_COMB (@lem5423679 A) (@lem5423676 A B)). Qed.
Lemma lem5423687 (f : nat -> nat) (s : nat -> Prop) : (s = (term65 f s)) = (s = (term65 f s)).
Proof. exact (eq_refl (s = (term65 f s))). Qed.
Lemma lem5423700 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term66 s f i j) = (term66 s f i j).
Proof. exact (eq_refl (term66 s f i j)). Qed.
Lemma lem5423701 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term67 s f i) = (term67 s f i).
Proof. exact (fun_ext (fun j : nat => @lem5423700 s f i j)). Qed.
Lemma lem5423702 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423703 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term68 s f i) = (term68 s f i).
Proof. exact (MK_COMB (@lem5423702) (@lem5423701 s f i)). Qed.
Lemma lem5423704 (s : nat -> Prop) (f : nat -> nat) : (term69 s f) = (term69 s f).
Proof. exact (fun_ext (fun i : nat => @lem5423703 s f i)). Qed.
Lemma lem5423705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423706 (s : nat -> Prop) (f : nat -> nat) : (term70 s f) = (term70 s f).
Proof. exact (MK_COMB (@lem5423705) (@lem5423704 s f)). Qed.
Lemma lem5423707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5423708 (s : nat -> Prop) (f : nat -> nat) : (term71 s f) = (term71 s f).
Proof. exact (MK_COMB (@lem5423707) (@lem5423706 s f)). Qed.
Lemma lem5423709 (f : nat -> nat) (s : nat -> Prop) : (term72 f s) = (term72 f s).
Proof. exact (MK_COMB (@lem5423708 s f) (@lem5423687 f s)). Qed.
Lemma lem5423710 (s : nat -> Prop) : (term73 s) = (term73 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5423709 f s)). Qed.
Lemma lem5423711 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5423712 (s : nat -> Prop) : (term74 s) = (term74 s).
Proof. exact (MK_COMB (@lem5423711) (@lem5423710 s)). Qed.
Lemma lem5423715 (s : nat -> Prop) : (term75 s) = (term75 s).
Proof. exact (eq_refl (term75 s)). Qed.
Lemma lem5423716 (s : nat -> Prop) : ((@FINITE nat s) = (term74 s)) = ((@FINITE nat s) = (term74 s)).
Proof. exact (MK_COMB (@lem5423715 s) (@lem5423712 s)). Qed.
Lemma lem5423717 : term76 = term76.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5423716 s)). Qed.
Lemma lem5423718 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5423719 : term12 = term12.
Proof. exact (MK_COMB (@lem5423718) (@lem5423717)). Qed.
Lemma lem5423720 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5423721 : term27 = term27.
Proof. exact (MK_COMB (@lem5423720) (@lem5423719)). Qed.
Lemma lem5423722 {A : Type'} (f : type1597 A) (s : type686 A) : (s = (term77 A f s)) = (s = (term77 A f s)).
Proof. exact (eq_refl (s = (term77 A f s))). Qed.
Lemma lem5423735 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term78 A s f i j) = (term78 A s f i j).
Proof. exact (eq_refl (term78 A s f i j)). Qed.
Lemma lem5423736 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term79 A s f i) = (term79 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5423735 A s f i j)). Qed.
Lemma lem5423737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423738 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term80 A s f i) = (term80 A s f i).
Proof. exact (MK_COMB (@lem5423737) (@lem5423736 A s f i)). Qed.
Lemma lem5423739 {A : Type'} (s : type686 A) (f : type1597 A) : (term81 A s f) = (term81 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5423738 A s f i)). Qed.
Lemma lem5423740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423741 {A : Type'} (s : type686 A) (f : type1597 A) : (term82 A s f) = (term82 A s f).
Proof. exact (MK_COMB (@lem5423740) (@lem5423739 A s f)). Qed.
Lemma lem5423742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5423743 {A : Type'} (s : type686 A) (f : type1597 A) : (term83 A s f) = (term83 A s f).
Proof. exact (MK_COMB (@lem5423742) (@lem5423741 A s f)). Qed.
Lemma lem5423744 {A : Type'} (f : type1597 A) (s : type686 A) : (term84 A f s) = (term84 A f s).
Proof. exact (MK_COMB (@lem5423743 A s f) (@lem5423722 A f s)). Qed.
Lemma lem5423745 {A : Type'} (s : type686 A) : (term85 A s) = (term85 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5423744 A f s)). Qed.
Lemma lem5423746 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem5423747 {A : Type'} (s : type686 A) : (term86 A s) = (term86 A s).
Proof. exact (MK_COMB (@lem5423746 A) (@lem5423745 A s)). Qed.
Lemma lem5423750 {A : Type'} (s : type686 A) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem5423751 {A : Type'} (s : type686 A) : ((@FINITE (A -> Prop) s) = (term86 A s)) = ((@FINITE (A -> Prop) s) = (term86 A s)).
Proof. exact (MK_COMB (@lem5423750 A s) (@lem5423747 A s)). Qed.
Lemma lem5423752 {A : Type'} : (term88 A) = (term88 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5423751 A s)). Qed.
Lemma lem5423753 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5423754 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem5423753 A) (@lem5423752 A)). Qed.
Lemma lem5423755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423756 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem5423755) (@lem5423754 A)). Qed.
Lemma lem5423757 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem5423756 A) (@lem5423721)). Qed.
Lemma lem5423758 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term89 A f s)) = (s = (term89 A f s)).
Proof. exact (eq_refl (s = (term89 A f s))). Qed.
Lemma lem5423771 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term90 A s f i j) = (term90 A s f i j).
Proof. exact (eq_refl (term90 A s f i j)). Qed.
Lemma lem5423772 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term91 A s f i) = (term91 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5423771 A s f i j)). Qed.
Lemma lem5423773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423774 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term92 A s f i) = (term92 A s f i).
Proof. exact (MK_COMB (@lem5423773) (@lem5423772 A s f i)). Qed.
Lemma lem5423775 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term93 A s f) = (term93 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5423774 A s f i)). Qed.
Lemma lem5423776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423777 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term94 A s f) = (term94 A s f).
Proof. exact (MK_COMB (@lem5423776) (@lem5423775 A s f)). Qed.
Lemma lem5423778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5423779 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term95 A s f) = (term95 A s f).
Proof. exact (MK_COMB (@lem5423778) (@lem5423777 A s f)). Qed.
Lemma lem5423780 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term96 A f s) = (term96 A f s).
Proof. exact (MK_COMB (@lem5423779 A s f) (@lem5423758 A f s)). Qed.
Lemma lem5423781 {A : Type'} (s : A -> Prop) : (term97 A s) = (term97 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5423780 A f s)). Qed.
Lemma lem5423782 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5423783 {A : Type'} (s : A -> Prop) : (term98 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem5423782 A) (@lem5423781 A s)). Qed.
Lemma lem5423786 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (eq_refl (term99 A s)). Qed.
Lemma lem5423787 {A : Type'} (s : A -> Prop) : ((@FINITE A s) = (term98 A s)) = ((@FINITE A s) = (term98 A s)).
Proof. exact (MK_COMB (@lem5423786 A s) (@lem5423783 A s)). Qed.
Lemma lem5423788 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423787 A s)). Qed.
Lemma lem5423789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423790 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem5423789 A) (@lem5423788 A)). Qed.
Lemma lem5423791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423792 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem5423791) (@lem5423790 A)). Qed.
Lemma lem5423793 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem5423792 A) (@lem5423757 A)). Qed.
Lemma lem5423794 (m : nat) (n : nat) : (term101 m n) = (term101 m n).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem5423795 (m : nat) : (term102 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem5423794 m n)). Qed.
Lemma lem5423796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423797 (m : nat) : (term103 m) = (term103 m).
Proof. exact (MK_COMB (@lem5423796) (@lem5423795 m)). Qed.
Lemma lem5423798 : term104 = term104.
Proof. exact (fun_ext (fun m : nat => @lem5423797 m)). Qed.
Lemma lem5423799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423800 : term105 = term105.
Proof. exact (MK_COMB (@lem5423799) (@lem5423798)). Qed.
Lemma lem5423801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423802 : term34 = term34.
Proof. exact (MK_COMB (@lem5423801) (@lem5423800)). Qed.
Lemma lem5423803 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem5423802) (@lem5423793 A)). Qed.
Lemma lem5423808 (f : nat -> nat) (s : nat -> Prop) : (term106 f s) = (term106 f s).
Proof. exact (eq_refl (term106 f s)). Qed.
Lemma lem5423809 (f : nat -> nat) : (term107 f) = (term107 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5423808 f s)). Qed.
Lemma lem5423810 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5423811 (f : nat -> nat) : (term108 f) = (term108 f).
Proof. exact (MK_COMB (@lem5423810) (@lem5423809 f)). Qed.
Lemma lem5423812 : term109 = term109.
Proof. exact (fun_ext (fun f : nat -> nat => @lem5423811 f)). Qed.
Lemma lem5423813 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5423814 : term20 = term20.
Proof. exact (MK_COMB (@lem5423813) (@lem5423812)). Qed.
Lemma lem5423815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423816 : term37 = term37.
Proof. exact (MK_COMB (@lem5423815) (@lem5423814)). Qed.
Lemma lem5423817 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (MK_COMB (@lem5423816) (@lem5423803 A)). Qed.
Lemma lem5423822 {A : Type'} (f : type1597 A) (s : nat -> Prop) : (term110 A f s) = (term110 A f s).
Proof. exact (eq_refl (term110 A f s)). Qed.
Lemma lem5423823 {A : Type'} (f : type1597 A) : (term111 A f) = (term111 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5423822 A f s)). Qed.
Lemma lem5423824 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5423825 {A : Type'} (f : type1597 A) : (term112 A f) = (term112 A f).
Proof. exact (MK_COMB (@lem5423824) (@lem5423823 A f)). Qed.
Lemma lem5423826 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (fun_ext (fun f : type1597 A => @lem5423825 A f)). Qed.
Lemma lem5423827 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5423828 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem5423827 A) (@lem5423826 A)). Qed.
Lemma lem5423829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423830 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem5423829) (@lem5423828 A)). Qed.
Lemma lem5423831 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (MK_COMB (@lem5423830 A) (@lem5423817 A)). Qed.
Lemma lem5423836 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term114 B f s) = (term114 B f s).
Proof. exact (eq_refl (term114 B f s)). Qed.
Lemma lem5423837 {B : Type'} (f : nat -> B) : (term115 B f) = (term115 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5423836 B f s)). Qed.
Lemma lem5423838 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5423839 {B : Type'} (f : nat -> B) : (term116 B f) = (term116 B f).
Proof. exact (MK_COMB (@lem5423838) (@lem5423837 B f)). Qed.
Lemma lem5423840 {B : Type'} : (term117 B) = (term117 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem5423839 B f)). Qed.
Lemma lem5423841 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem5423842 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem5423841 B) (@lem5423840 B)). Qed.
Lemma lem5423843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423844 {B : Type'} : (term43 B) = (term43 B).
Proof. exact (MK_COMB (@lem5423843) (@lem5423842 B)). Qed.
Lemma lem5423845 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem5423844 B) (@lem5423831 A)). Qed.
Lemma lem5423850 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term114 A f s) = (term114 A f s).
Proof. exact (eq_refl (term114 A f s)). Qed.
Lemma lem5423851 {A : Type'} (f : nat -> A) : (term115 A f) = (term115 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5423850 A f s)). Qed.
Lemma lem5423852 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5423853 {A : Type'} (f : nat -> A) : (term116 A f) = (term116 A f).
Proof. exact (MK_COMB (@lem5423852) (@lem5423851 A f)). Qed.
Lemma lem5423854 {A : Type'} : (term117 A) = (term117 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5423853 A f)). Qed.
Lemma lem5423855 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5423856 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem5423855 A) (@lem5423854 A)). Qed.
Lemma lem5423857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423858 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (MK_COMB (@lem5423857) (@lem5423856 A)). Qed.
Lemma lem5423859 {A B : Type'} : (term47 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem5423858 A) (@lem5423845 A B)). Qed.
Lemma lem5423864 {A B : Type'} (f : type685 A B) (s : type686 A) : (term118 A B f s) = (term118 A B f s).
Proof. exact (eq_refl (term118 A B f s)). Qed.
Lemma lem5423865 {A B : Type'} (f : type685 A B) : (term119 A B f) = (term119 A B f).
Proof. exact (fun_ext (fun s : type686 A => @lem5423864 A B f s)). Qed.
Lemma lem5423866 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5423867 {A B : Type'} (f : type685 A B) : (term120 A B f) = (term120 A B f).
Proof. exact (MK_COMB (@lem5423866 A) (@lem5423865 A B f)). Qed.
Lemma lem5423868 {A B : Type'} : (term121 A B) = (term121 A B).
Proof. exact (fun_ext (fun f : type685 A B => @lem5423867 A B f)). Qed.
Lemma lem5423869 {A B : Type'} : (@all ((A -> Prop) -> B)) = (@all ((A -> Prop) -> B)).
Proof. exact (eq_refl (@all ((A -> Prop) -> B))). Qed.
Lemma lem5423870 {A B : Type'} : (term16 A B) = (term16 A B).
Proof. exact (MK_COMB (@lem5423869 A B) (@lem5423868 A B)). Qed.
Lemma lem5423871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423872 {A B : Type'} : (term48 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem5423871) (@lem5423870 A B)). Qed.
Lemma lem5423873 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem5423872 A B) (@lem5423859 A B)). Qed.
Lemma lem5423878 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term122 A f s) = (term122 A f s).
Proof. exact (eq_refl (term122 A f s)). Qed.
Lemma lem5423879 {A : Type'} (f : A -> nat) : (term123 A f) = (term123 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423878 A f s)). Qed.
Lemma lem5423880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423881 {A : Type'} (f : A -> nat) : (term124 A f) = (term124 A f).
Proof. exact (MK_COMB (@lem5423880 A) (@lem5423879 A f)). Qed.
Lemma lem5423882 {A : Type'} : (term125 A) = (term125 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem5423881 A f)). Qed.
Lemma lem5423883 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem5423884 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem5423883 A) (@lem5423882 A)). Qed.
Lemma lem5423885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423886 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem5423885) (@lem5423884 A)). Qed.
Lemma lem5423887 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem5423886 A) (@lem5423873 A B)). Qed.
Lemma lem5423892 {A : Type'} (f : type1402 A) (s : A -> Prop) : (term126 A f s) = (term126 A f s).
Proof. exact (eq_refl (term126 A f s)). Qed.
Lemma lem5423893 {A : Type'} (f : type1402 A) : (term127 A f) = (term127 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423892 A f s)). Qed.
Lemma lem5423894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423895 {A : Type'} (f : type1402 A) : (term128 A f) = (term128 A f).
Proof. exact (MK_COMB (@lem5423894 A) (@lem5423893 A f)). Qed.
Lemma lem5423896 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (fun_ext (fun f : type1402 A => @lem5423895 A f)). Qed.
Lemma lem5423897 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5423898 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem5423897 A) (@lem5423896 A)). Qed.
Lemma lem5423899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423900 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (MK_COMB (@lem5423899) (@lem5423898 A)). Qed.
Lemma lem5423901 {A B : Type'} : (term56 A B) = (term56 A B).
Proof. exact (MK_COMB (@lem5423900 A) (@lem5423887 A B)). Qed.
Lemma lem5423906 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term130 A B f s) = (term130 A B f s).
Proof. exact (eq_refl (term130 A B f s)). Qed.
Lemma lem5423907 {A B : Type'} (f : A -> B) : (term131 A B f) = (term131 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423906 A B f s)). Qed.
Lemma lem5423908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423909 {A B : Type'} (f : A -> B) : (term132 A B f) = (term132 A B f).
Proof. exact (MK_COMB (@lem5423908 A) (@lem5423907 A B f)). Qed.
Lemma lem5423910 {A B : Type'} : (term133 A B) = (term133 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5423909 A B f)). Qed.
Lemma lem5423911 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5423912 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem5423911 A B) (@lem5423910 A B)). Qed.
Lemma lem5423913 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423914 {A B : Type'} : (term57 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem5423913) (@lem5423912 A B)). Qed.
Lemma lem5423915 {A B : Type'} : (term59 A B) = (term59 A B).
Proof. exact (MK_COMB (@lem5423914 A B) (@lem5423901 A B)). Qed.
Lemma lem5423920 {A : Type'} (f : A -> A) (s : A -> Prop) : (term134 A f s) = (term134 A f s).
Proof. exact (eq_refl (term134 A f s)). Qed.
Lemma lem5423921 {A : Type'} (f : A -> A) : (term135 A f) = (term135 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423920 A f s)). Qed.
Lemma lem5423922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423923 {A : Type'} (f : A -> A) : (term136 A f) = (term136 A f).
Proof. exact (MK_COMB (@lem5423922 A) (@lem5423921 A f)). Qed.
Lemma lem5423924 {A : Type'} : (term137 A) = (term137 A).
Proof. exact (fun_ext (fun f : A -> A => @lem5423923 A f)). Qed.
Lemma lem5423925 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5423926 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (MK_COMB (@lem5423925 A) (@lem5423924 A)). Qed.
Lemma lem5423927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423928 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (MK_COMB (@lem5423927) (@lem5423926 A)). Qed.
Lemma lem5423929 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (MK_COMB (@lem5423928 A) (@lem5423915 A B)). Qed.
Lemma lem5423934 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term138 A s f k) = (term138 A s f k).
Proof. exact (eq_refl (term138 A s f k)). Qed.
Lemma lem5423947 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term139 A k f i j) = (term139 A k f i j).
Proof. exact (eq_refl (term139 A k f i j)). Qed.
Lemma lem5423948 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term140 A k f i) = (term140 A k f i).
Proof. exact (fun_ext (fun j : nat => @lem5423947 A k f i j)). Qed.
Lemma lem5423949 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423950 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term141 A k f i) = (term141 A k f i).
Proof. exact (MK_COMB (@lem5423949) (@lem5423948 A k f i)). Qed.
Lemma lem5423951 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term142 A k f) = (term142 A k f).
Proof. exact (fun_ext (fun i : nat => @lem5423950 A k f i)). Qed.
Lemma lem5423952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5423953 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term143 A k f) = (term143 A k f).
Proof. exact (MK_COMB (@lem5423952) (@lem5423951 A k f)). Qed.
Lemma lem5423954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5423955 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term144 A k f) = (term144 A k f).
Proof. exact (MK_COMB (@lem5423954) (@lem5423953 A k f)). Qed.
Lemma lem5423956 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term145 A s f k) = (term145 A s f k).
Proof. exact (MK_COMB (@lem5423955 A k f) (@lem5423934 A s f k)). Qed.
Lemma lem5423957 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term146 A s k) = (term146 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5423956 A s f k)). Qed.
Lemma lem5423958 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5423959 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term147 A s k) = (term147 A s k).
Proof. exact (MK_COMB (@lem5423958 A) (@lem5423957 A s k)). Qed.
Lemma lem5423960 {A : Type'} (s : A -> Prop) : (term148 A s) = (term148 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5423959 A s k)). Qed.
Lemma lem5423961 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5423962 {A : Type'} (s : A -> Prop) : (term149 A s) = (term149 A s).
Proof. exact (MK_COMB (@lem5423961) (@lem5423960 A s)). Qed.
Lemma lem5423965 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (eq_refl (term99 A s)). Qed.
Lemma lem5423966 {A : Type'} (s : A -> Prop) : ((@FINITE A s) = (term149 A s)) = ((@FINITE A s) = (term149 A s)).
Proof. exact (MK_COMB (@lem5423965 A s) (@lem5423962 A s)). Qed.
Lemma lem5423967 {A : Type'} : (term150 A) = (term150 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5423966 A s)). Qed.
Lemma lem5423968 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5423969 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem5423968 A) (@lem5423967 A)). Qed.
Lemma lem5423970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5423971 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem5423970) (@lem5423969 A)). Qed.
Lemma lem5423972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423973 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem5423972) (@lem5423971 A)). Qed.
Lemma lem5423974 {A B : Type'} : (term64 A B) = (term64 A B).
Proof. exact (MK_COMB (@lem5423973 A) (@lem5423929 A B)). Qed.
Lemma lem5424277 {A B : Type'} : (term22 A B) = (term64 A B).
Proof. exact (TRANS (@lem5423686 A B) (@lem5423974 A B)). Qed.
Lemma lem5424278 {A B : Type'} : (term64 A B) = (term22 A B).
Proof. exact (SYM (@lem5424277 A B)). Qed.
Lemma lem5424279 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem5424285 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem5424289 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem5424290 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem5424291 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem5424292 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5424305 {A : Type'} (k : nat -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term151 A k i f j) = (term152 A k i f j).
Proof. exact (@lem17045 (@IN nat j k) ((f i) = (f j))). Qed.
Lemma lem5424310 (i : nat) (k : nat -> Prop) : (term153 i k) = (term153 i k).
Proof. exact (eq_refl (term153 i k)). Qed.
Lemma lem5424311 {A : Type'} (k : nat -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term154 A k i f j) = (term155 A k i f j).
Proof. exact (MK_COMB (@lem5424310 i k) (@lem5424305 A k i f j)). Qed.
Lemma lem5424312 {A : Type'} (k : nat -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term156 A k i f j) = (term154 A k i f j).
Proof. exact (@lem17045 (@IN nat i k) (term157 A k i f j)). Qed.
Lemma lem5424313 {A : Type'} (k : nat -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term156 A k i f j) = (term155 A k i f j).
Proof. exact (TRANS (@lem5424312 A k i f j) (@lem5424311 A k i f j)). Qed.
Lemma lem5424318 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5424323 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term158 A k f i j) = (term159 A k f i j).
Proof. exact (@lem17362 (term160 A k i f j) (i = j)). Qed.
Lemma lem5424324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424325 {A : Type'} (k : nat -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term161 A k i f j) = (term162 A k i f j).
Proof. exact (MK_COMB (@lem5424324) (@lem5424313 A k i f j)). Qed.
Lemma lem5424326 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term163 A k f i j) = (term164 A k f i j).
Proof. exact (MK_COMB (@lem5424325 A k i f j) (@lem5424318 i j)). Qed.
Lemma lem5424327 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term139 A k f i j) = (term163 A k f i j).
Proof. exact (@lem17265 (term160 A k i f j) (i = j)). Qed.
Lemma lem5424328 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term139 A k f i j) = (term164 A k f i j).
Proof. exact (TRANS (@lem5424327 A k f i j) (@lem5424326 A k f i j)). Qed.
Lemma lem5424329 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5424330 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term167 A k f i) = (term168 A k f i).
Proof. exact (@lem5424329 (term140 A k f i)). Qed.
Lemma lem5424331 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term169 A k f i j) = (term139 A k f i j).
Proof. exact (eq_refl (term169 A k f i j)). Qed.
Lemma lem5424332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5424333 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term170 A k f i j) = (term158 A k f i j).
Proof. exact (MK_COMB (@lem5424332) (@lem5424331 A k f i j)). Qed.
Lemma lem5424334 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term170 A k f i j) = (term159 A k f i j).
Proof. exact (TRANS (@lem5424333 A k f i j) (@lem5424323 A k f i j)). Qed.
Lemma lem5424335 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term171 A k f i) = (term172 A k f i).
Proof. exact (fun_ext (fun j : nat => @lem5424334 A k f i j)). Qed.
Lemma lem5424336 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424337 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term168 A k f i) = (term173 A k f i).
Proof. exact (MK_COMB (@lem5424336) (@lem5424335 A k f i)). Qed.
Lemma lem5424338 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term167 A k f i) = (term173 A k f i).
Proof. exact (TRANS (@lem5424330 A k f i) (@lem5424337 A k f i)). Qed.
Lemma lem5424339 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term140 A k f i) = (term174 A k f i).
Proof. exact (fun_ext (fun j : nat => @lem5424328 A k f i j)). Qed.
Lemma lem5424340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5424341 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term141 A k f i) = (term175 A k f i).
Proof. exact (MK_COMB (@lem5424340) (@lem5424339 A k f i)). Qed.
Lemma lem5424342 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5424343 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term176 A k f) = (term177 A k f).
Proof. exact (@lem5424342 (term142 A k f)). Qed.
Lemma lem5424344 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term178 A k f i) = (term141 A k f i).
Proof. exact (eq_refl (term178 A k f i)). Qed.
Lemma lem5424345 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5424346 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term179 A k f i) = (term167 A k f i).
Proof. exact (MK_COMB (@lem5424345) (@lem5424344 A k f i)). Qed.
Lemma lem5424347 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term179 A k f i) = (term173 A k f i).
Proof. exact (TRANS (@lem5424346 A k f i) (@lem5424338 A k f i)). Qed.
Lemma lem5424348 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term180 A k f) = (term181 A k f).
Proof. exact (fun_ext (fun i : nat => @lem5424347 A k f i)). Qed.
Lemma lem5424349 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424350 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term177 A k f) = (term182 A k f).
Proof. exact (MK_COMB (@lem5424349) (@lem5424348 A k f)). Qed.
Lemma lem5424351 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term176 A k f) = (term182 A k f).
Proof. exact (TRANS (@lem5424343 A k f) (@lem5424350 A k f)). Qed.
Lemma lem5424352 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term142 A k f) = (term183 A k f).
Proof. exact (fun_ext (fun i : nat => @lem5424341 A k f i)). Qed.
Lemma lem5424353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5424354 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term143 A k f) = (term184 A k f).
Proof. exact (MK_COMB (@lem5424353) (@lem5424352 A k f)). Qed.
Lemma lem5424363 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term185 A s f k) = (term186 A s f k).
Proof. exact (@lem17045 (@FINITE nat k) (s = (@IMAGE nat A f k))). Qed.
Lemma lem5424366 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term138 A s f k) = (term138 A s f k).
Proof. exact (eq_refl (term138 A s f k)). Qed.
Lemma lem5424367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424368 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term187 A k f) = (term188 A k f).
Proof. exact (MK_COMB (@lem5424367) (@lem5424351 A k f)). Qed.
Lemma lem5424369 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term189 A s f k) = (term190 A s f k).
Proof. exact (MK_COMB (@lem5424368 A k f) (@lem5424363 A s f k)). Qed.
Lemma lem5424370 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term191 A s f k) = (term189 A s f k).
Proof. exact (@lem17045 (term143 A k f) (term138 A s f k)). Qed.
Lemma lem5424371 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term191 A s f k) = (term190 A s f k).
Proof. exact (TRANS (@lem5424370 A s f k) (@lem5424369 A s f k)). Qed.
Lemma lem5424372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5424373 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term144 A k f) = (term192 A k f).
Proof. exact (MK_COMB (@lem5424372) (@lem5424354 A k f)). Qed.
Lemma lem5424374 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term145 A s f k) = (term193 A s f k).
Proof. exact (MK_COMB (@lem5424373 A k f) (@lem5424366 A s f k)). Qed.
Lemma lem5424375 {A : Type'} (P : type976 A) : (term194 A P) = (term195 A P).
Proof. exact (@lem18394 (nat -> A) P). Qed.
Lemma lem5424376 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term196 A s k) = (term197 A s k).
Proof. exact (@lem5424375 A (term146 A s k)). Qed.
Lemma lem5424377 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term198 A s k f) = (term145 A s f k).
Proof. exact (eq_refl (term198 A s k f)). Qed.
Lemma lem5424378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5424379 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term199 A s k f) = (term191 A s f k).
Proof. exact (MK_COMB (@lem5424378) (@lem5424377 A s f k)). Qed.
Lemma lem5424380 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term199 A s k f) = (term190 A s f k).
Proof. exact (TRANS (@lem5424379 A s f k) (@lem5424371 A s f k)). Qed.
Lemma lem5424381 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term200 A s k) = (term201 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424380 A s f k)). Qed.
Lemma lem5424382 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424383 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term197 A s k) = (term202 A s k).
Proof. exact (MK_COMB (@lem5424382 A) (@lem5424381 A s k)). Qed.
Lemma lem5424384 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term196 A s k) = (term202 A s k).
Proof. exact (TRANS (@lem5424376 A s k) (@lem5424383 A s k)). Qed.
Lemma lem5424385 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term146 A s k) = (term203 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424374 A s f k)). Qed.
Lemma lem5424386 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5424387 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term147 A s k) = (term204 A s k).
Proof. exact (MK_COMB (@lem5424386 A) (@lem5424385 A s k)). Qed.
Lemma lem5424388 (P : type993) : (term205 P) = (term206 P).
Proof. exact (@lem18394 (nat -> Prop) P). Qed.
Lemma lem5424389 {A : Type'} (s : A -> Prop) : (term207 A s) = (term208 A s).
Proof. exact (@lem5424388 (term148 A s)). Qed.
Lemma lem5424390 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term209 A s k) = (term147 A s k).
Proof. exact (eq_refl (term209 A s k)). Qed.
Lemma lem5424391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5424392 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term210 A s k) = (term196 A s k).
Proof. exact (MK_COMB (@lem5424391) (@lem5424390 A s k)). Qed.
Lemma lem5424393 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term210 A s k) = (term202 A s k).
Proof. exact (TRANS (@lem5424392 A s k) (@lem5424384 A s k)). Qed.
Lemma lem5424394 {A : Type'} (s : A -> Prop) : (term211 A s) = (term212 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424393 A s k)). Qed.
Lemma lem5424395 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424396 {A : Type'} (s : A -> Prop) : (term208 A s) = (term213 A s).
Proof. exact (MK_COMB (@lem5424395) (@lem5424394 A s)). Qed.
Lemma lem5424397 {A : Type'} (s : A -> Prop) : (term207 A s) = (term213 A s).
Proof. exact (TRANS (@lem5424389 A s) (@lem5424396 A s)). Qed.
Lemma lem5424398 {A : Type'} (s : A -> Prop) : (term148 A s) = (term214 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424387 A s k)). Qed.
Lemma lem5424399 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5424400 {A : Type'} (s : A -> Prop) : (term149 A s) = (term215 A s).
Proof. exact (MK_COMB (@lem5424399) (@lem5424398 A s)). Qed.
Lemma lem5424402 {A : Type'} (s : A -> Prop) : (term216 A s) = (term216 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem5424403 {A : Type'} (s : A -> Prop) : (term217 A s) = (term218 A s).
Proof. exact (MK_COMB (@lem5424402 A s) (@lem5424400 A s)). Qed.
Lemma lem5424405 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424406 {A : Type'} (s : A -> Prop) : (term220 A s) = (term221 A s).
Proof. exact (MK_COMB (@lem5424405 A s) (@lem5424397 A s)). Qed.
Lemma lem5424407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424408 {A : Type'} (s : A -> Prop) : (term222 A s) = (term223 A s).
Proof. exact (MK_COMB (@lem5424407) (@lem5424406 A s)). Qed.
Lemma lem5424409 {A : Type'} (s : A -> Prop) : (term224 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem5424408 A s) (@lem5424403 A s)). Qed.
Lemma lem5424410 {A : Type'} (s : A -> Prop) : (term226 A s) = (term224 A s).
Proof. exact (@lem17646 (@FINITE A s) (term149 A s)). Qed.
Lemma lem5424411 {A : Type'} (s : A -> Prop) : (term226 A s) = (term225 A s).
Proof. exact (TRANS (@lem5424410 A s) (@lem5424409 A s)). Qed.
Lemma lem5424412 {A : Type'} (P : type686 A) : (term227 A P) = (term228 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem5424413 {A : Type'} : (term10 A) = (term229 A).
Proof. exact (@lem5424412 A (term150 A)). Qed.
Lemma lem5424414 {A : Type'} (s : A -> Prop) : (term230 A s) = ((@FINITE A s) = (term149 A s)).
Proof. exact (eq_refl (term230 A s)). Qed.
Lemma lem5424415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5424416 {A : Type'} (s : A -> Prop) : (term231 A s) = (term226 A s).
Proof. exact (MK_COMB (@lem5424415) (@lem5424414 A s)). Qed.
Lemma lem5424417 {A : Type'} (s : A -> Prop) : (term231 A s) = (term225 A s).
Proof. exact (TRANS (@lem5424416 A s) (@lem5424411 A s)). Qed.
Lemma lem5424418 {A : Type'} : (term232 A) = (term233 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5424417 A s)). Qed.
Lemma lem5424419 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5424420 {A : Type'} : (term229 A) = (term234 A).
Proof. exact (MK_COMB (@lem5424419 A) (@lem5424418 A)). Qed.
Lemma lem5424421 {A : Type'} : (term10 A) = (term234 A).
Proof. exact (TRANS (@lem5424413 A) (@lem5424420 A)). Qed.
Lemma lem5424423 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5424424 {A : Type'} (P : type686 A) (Q : type686 A) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem5424423 (A -> Prop) P Q). Qed.
Lemma lem5424425 {A : Type'} : (term239 A) = (term240 A).
Proof. exact (@lem5424424 A (term241 A) (term242 A)). Qed.
Lemma lem5424426 {A : Type'} (s : A -> Prop) : (term243 A s) = (term221 A s).
Proof. exact (eq_refl (term243 A s)). Qed.
Lemma lem5424427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424428 {A : Type'} (s : A -> Prop) : (term244 A s) = (term223 A s).
Proof. exact (MK_COMB (@lem5424427) (@lem5424426 A s)). Qed.
Lemma lem5424429 {A : Type'} (s : A -> Prop) : (term245 A s) = (term218 A s).
Proof. exact (eq_refl (term245 A s)). Qed.
Lemma lem5424430 {A : Type'} (s : A -> Prop) : (term246 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem5424428 A s) (@lem5424429 A s)). Qed.
Lemma lem5424431 {A : Type'} : (term247 A) = (term233 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5424430 A s)). Qed.
Lemma lem5424432 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5424433 {A : Type'} : (term239 A) = (term234 A).
Proof. exact (MK_COMB (@lem5424432 A) (@lem5424431 A)). Qed.
Lemma lem5424434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424435 {A : Type'} : (term248 A) = (term249 A).
Proof. exact (MK_COMB (@lem5424434) (@lem5424433 A)). Qed.
Lemma lem5424436 {A : Type'} (s : A -> Prop) : (term243 A s) = (term221 A s).
Proof. exact (eq_refl (term243 A s)). Qed.
Lemma lem5424437 {A : Type'} : (term250 A) = (term241 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5424436 A s)). Qed.
Lemma lem5424438 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5424439 {A : Type'} : (term251 A) = (term252 A).
Proof. exact (MK_COMB (@lem5424438 A) (@lem5424437 A)). Qed.
Lemma lem5424440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424441 {A : Type'} : (term253 A) = (term254 A).
Proof. exact (MK_COMB (@lem5424440) (@lem5424439 A)). Qed.
Lemma lem5424442 {A : Type'} (s : A -> Prop) : (term245 A s) = (term218 A s).
Proof. exact (eq_refl (term245 A s)). Qed.
Lemma lem5424443 {A : Type'} : (term255 A) = (term242 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5424442 A s)). Qed.
Lemma lem5424444 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5424445 {A : Type'} : (term256 A) = (term257 A).
Proof. exact (MK_COMB (@lem5424444 A) (@lem5424443 A)). Qed.
Lemma lem5424446 {A : Type'} : (term240 A) = (term258 A).
Proof. exact (MK_COMB (@lem5424441 A) (@lem5424445 A)). Qed.
Lemma lem5424447 {A : Type'} : ((term239 A) = (term240 A)) = ((term234 A) = (term258 A)).
Proof. exact (MK_COMB (@lem5424435 A) (@lem5424446 A)). Qed.
Lemma lem5424448 {A : Type'} : (term234 A) = (term258 A).
Proof. exact (EQ_MP (@lem5424447 A) (@lem5424425 A)). Qed.
Lemma lem5424734 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5424735 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5424734 nat P Q). Qed.
Lemma lem5424736 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term263 A s f k) = (term264 A s f k).
Proof. exact (@lem5424735 (term181 A k f) (term186 A s f k)). Qed.
Lemma lem5424737 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term265 A k f i) = (term173 A k f i).
Proof. exact (eq_refl (term265 A k f i)). Qed.
Lemma lem5424738 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term266 A k f) = (term181 A k f).
Proof. exact (fun_ext (fun i : nat => @lem5424737 A k f i)). Qed.
Lemma lem5424739 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424740 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term267 A k f) = (term182 A k f).
Proof. exact (MK_COMB (@lem5424739) (@lem5424738 A k f)). Qed.
Lemma lem5424741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424742 {A : Type'} (k : nat -> Prop) (f : nat -> A) : (term268 A k f) = (term188 A k f).
Proof. exact (MK_COMB (@lem5424741) (@lem5424740 A k f)). Qed.
Lemma lem5424743 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term186 A s f k) = (term186 A s f k).
Proof. exact (eq_refl (term186 A s f k)). Qed.
Lemma lem5424744 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term263 A s f k) = (term190 A s f k).
Proof. exact (MK_COMB (@lem5424742 A k f) (@lem5424743 A s f k)). Qed.
Lemma lem5424745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424746 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term269 A s f k) = (term270 A s f k).
Proof. exact (MK_COMB (@lem5424745) (@lem5424744 A s f k)). Qed.
Lemma lem5424747 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term265 A k f i) = (term173 A k f i).
Proof. exact (eq_refl (term265 A k f i)). Qed.
Lemma lem5424748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424749 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term271 A k f i) = (term272 A k f i).
Proof. exact (MK_COMB (@lem5424748) (@lem5424747 A k f i)). Qed.
Lemma lem5424750 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term186 A s f k) = (term186 A s f k).
Proof. exact (eq_refl (term186 A s f k)). Qed.
Lemma lem5424751 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term273 A i s f k) = (term274 A i s f k).
Proof. exact (MK_COMB (@lem5424749 A k f i) (@lem5424750 A s f k)). Qed.
Lemma lem5424752 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term275 A s f k) = (term276 A s f k).
Proof. exact (fun_ext (fun i : nat => @lem5424751 A i s f k)). Qed.
Lemma lem5424753 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424754 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term264 A s f k) = (term277 A s f k).
Proof. exact (MK_COMB (@lem5424753) (@lem5424752 A s f k)). Qed.
Lemma lem5424755 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : ((term263 A s f k) = (term264 A s f k)) = ((term190 A s f k) = (term277 A s f k)).
Proof. exact (MK_COMB (@lem5424746 A s f k) (@lem5424754 A s f k)). Qed.
Lemma lem5424756 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term190 A s f k) = (term277 A s f k).
Proof. exact (EQ_MP (@lem5424755 A s f k) (@lem5424736 A s f k)). Qed.
Lemma lem5424758 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5424759 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5424758 nat P Q). Qed.
Lemma lem5424760 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term278 A i s f k) = (term279 A i s f k).
Proof. exact (@lem5424759 (term172 A k f i) (term186 A s f k)). Qed.
Lemma lem5424761 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term280 A k f i j) = (term159 A k f i j).
Proof. exact (eq_refl (term280 A k f i j)). Qed.
Lemma lem5424762 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term281 A k f i) = (term172 A k f i).
Proof. exact (fun_ext (fun j : nat => @lem5424761 A k f i j)). Qed.
Lemma lem5424763 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424764 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term282 A k f i) = (term173 A k f i).
Proof. exact (MK_COMB (@lem5424763) (@lem5424762 A k f i)). Qed.
Lemma lem5424765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424766 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) : (term283 A k f i) = (term272 A k f i).
Proof. exact (MK_COMB (@lem5424765) (@lem5424764 A k f i)). Qed.
Lemma lem5424767 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term186 A s f k) = (term186 A s f k).
Proof. exact (eq_refl (term186 A s f k)). Qed.
Lemma lem5424768 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term278 A i s f k) = (term274 A i s f k).
Proof. exact (MK_COMB (@lem5424766 A k f i) (@lem5424767 A s f k)). Qed.
Lemma lem5424769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424770 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term284 A i s f k) = (term285 A i s f k).
Proof. exact (MK_COMB (@lem5424769) (@lem5424768 A i s f k)). Qed.
Lemma lem5424771 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term280 A k f i j) = (term159 A k f i j).
Proof. exact (eq_refl (term280 A k f i j)). Qed.
Lemma lem5424772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424773 {A : Type'} (k : nat -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term286 A k f i j) = (term287 A k f i j).
Proof. exact (MK_COMB (@lem5424772) (@lem5424771 A k f i j)). Qed.
Lemma lem5424774 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term186 A s f k) = (term186 A s f k).
Proof. exact (eq_refl (term186 A s f k)). Qed.
Lemma lem5424775 {A : Type'} (i : nat) (j : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term288 A i j s f k) = (term289 A i j s f k).
Proof. exact (MK_COMB (@lem5424773 A k f i j) (@lem5424774 A s f k)). Qed.
Lemma lem5424776 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term290 A i s f k) = (term291 A i s f k).
Proof. exact (fun_ext (fun j : nat => @lem5424775 A i j s f k)). Qed.
Lemma lem5424777 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424778 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term279 A i s f k) = (term292 A i s f k).
Proof. exact (MK_COMB (@lem5424777) (@lem5424776 A i s f k)). Qed.
Lemma lem5424779 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : ((term278 A i s f k) = (term279 A i s f k)) = ((term274 A i s f k) = (term292 A i s f k)).
Proof. exact (MK_COMB (@lem5424770 A i s f k) (@lem5424778 A i s f k)). Qed.
Lemma lem5424780 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term274 A i s f k) = (term292 A i s f k).
Proof. exact (EQ_MP (@lem5424779 A i s f k) (@lem5424760 A i s f k)). Qed.
Lemma lem5424781 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term276 A s f k) = (term293 A s f k).
Proof. exact (fun_ext (fun i : nat => @lem5424780 A i s f k)). Qed.
Lemma lem5424782 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424783 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term277 A s f k) = (term294 A s f k).
Proof. exact (MK_COMB (@lem5424782) (@lem5424781 A s f k)). Qed.
Lemma lem5424784 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term190 A s f k) = (term294 A s f k).
Proof. exact (TRANS (@lem5424756 A s f k) (@lem5424783 A s f k)). Qed.
Lemma lem5424785 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term201 A s k) = (term295 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424784 A s f k)). Qed.
Lemma lem5424786 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424787 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term202 A s k) = (term296 A s k).
Proof. exact (MK_COMB (@lem5424786 A) (@lem5424785 A s k)). Qed.
Lemma lem5424789 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5424790 {A : Type'} (P : type973 A) : (term299 A P) = (term300 A P).
Proof. exact (@lem5424789 (nat -> A) nat P). Qed.
Lemma lem5424791 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term301 A s k) = (term302 A s k).
Proof. exact (@lem5424790 A (term303 A s k)). Qed.
Lemma lem5424792 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term304 A s k f) = (term293 A s f k).
Proof. exact (eq_refl (term304 A s k f)). Qed.
Lemma lem5424793 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5424794 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) (i : nat) : (term305 A s k f i) = (term306 A s f k i).
Proof. exact (MK_COMB (@lem5424792 A s f k) (@lem5424793 i)). Qed.
Lemma lem5424795 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term306 A s f k i) = (term292 A i s f k).
Proof. exact (eq_refl (term306 A s f k i)). Qed.
Lemma lem5424796 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term305 A s k f i) = (term292 A i s f k).
Proof. exact (TRANS (@lem5424794 A s f k i) (@lem5424795 A i s f k)). Qed.
Lemma lem5424797 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term307 A s k f) = (term293 A s f k).
Proof. exact (fun_ext (fun i : nat => @lem5424796 A i s f k)). Qed.
Lemma lem5424798 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424799 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term308 A s k f) = (term294 A s f k).
Proof. exact (MK_COMB (@lem5424798) (@lem5424797 A s f k)). Qed.
Lemma lem5424800 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term309 A s k) = (term295 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424799 A s f k)). Qed.
Lemma lem5424801 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424802 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term301 A s k) = (term296 A s k).
Proof. exact (MK_COMB (@lem5424801 A) (@lem5424800 A s k)). Qed.
Lemma lem5424803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424804 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term310 A s k) = (term311 A s k).
Proof. exact (MK_COMB (@lem5424803) (@lem5424802 A s k)). Qed.
Lemma lem5424805 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term304 A s k f) = (term293 A s f k).
Proof. exact (eq_refl (term304 A s k f)). Qed.
Lemma lem5424806 {A : Type'} (i : type977 A) (f : nat -> A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem5424807 {A : Type'} (s : A -> Prop) (k : nat -> Prop) (i : type977 A) (f : nat -> A) : (term312 A s k i f) = (term313 A s k i f).
Proof. exact (MK_COMB (@lem5424805 A s f k) (@lem5424806 A i f)). Qed.
Lemma lem5424808 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term313 A s k i f) = (term314 A i s f k).
Proof. exact (eq_refl (term313 A s k i f)). Qed.
Lemma lem5424809 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term312 A s k i f) = (term314 A i s f k).
Proof. exact (TRANS (@lem5424807 A s k i f) (@lem5424808 A i s f k)). Qed.
Lemma lem5424810 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term315 A s k i) = (term316 A i s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424809 A i s f k)). Qed.
Lemma lem5424811 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424812 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term317 A s k i) = (term318 A i s k).
Proof. exact (MK_COMB (@lem5424811 A) (@lem5424810 A i s k)). Qed.
Lemma lem5424813 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term319 A s k) = (term320 A s k).
Proof. exact (fun_ext (fun i : type977 A => @lem5424812 A i s k)). Qed.
Lemma lem5424814 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5424815 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term302 A s k) = (term321 A s k).
Proof. exact (MK_COMB (@lem5424814 A) (@lem5424813 A s k)). Qed.
Lemma lem5424816 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : ((term301 A s k) = (term302 A s k)) = ((term296 A s k) = (term321 A s k)).
Proof. exact (MK_COMB (@lem5424804 A s k) (@lem5424815 A s k)). Qed.
Lemma lem5424817 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term296 A s k) = (term321 A s k).
Proof. exact (EQ_MP (@lem5424816 A s k) (@lem5424791 A s k)). Qed.
Lemma lem5424819 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5424820 {A : Type'} (P : type973 A) : (term299 A P) = (term300 A P).
Proof. exact (@lem5424819 (nat -> A) nat P). Qed.
Lemma lem5424821 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term322 A i s k) = (term323 A i s k).
Proof. exact (@lem5424820 A (term324 A i s k)). Qed.
Lemma lem5424822 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term325 A i s k f) = (term326 A i s f k).
Proof. exact (eq_refl (term325 A i s k f)). Qed.
Lemma lem5424823 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5424824 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) (j : nat) : (term327 A i s k f j) = (term328 A i s f k j).
Proof. exact (MK_COMB (@lem5424822 A i s f k) (@lem5424823 j)). Qed.
Lemma lem5424825 {A : Type'} (i : type977 A) (j : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term328 A i s f k j) = (term329 A i j s f k).
Proof. exact (eq_refl (term328 A i s f k j)). Qed.
Lemma lem5424826 {A : Type'} (i : type977 A) (j : nat) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term327 A i s k f j) = (term329 A i j s f k).
Proof. exact (TRANS (@lem5424824 A i s f k j) (@lem5424825 A i j s f k)). Qed.
Lemma lem5424827 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term330 A i s k f) = (term326 A i s f k).
Proof. exact (fun_ext (fun j : nat => @lem5424826 A i j s f k)). Qed.
Lemma lem5424828 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5424829 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term331 A i s k f) = (term314 A i s f k).
Proof. exact (MK_COMB (@lem5424828) (@lem5424827 A i s f k)). Qed.
Lemma lem5424830 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term332 A i s k) = (term316 A i s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424829 A i s f k)). Qed.
Lemma lem5424831 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424832 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term322 A i s k) = (term318 A i s k).
Proof. exact (MK_COMB (@lem5424831 A) (@lem5424830 A i s k)). Qed.
Lemma lem5424833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424834 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term333 A i s k) = (term334 A i s k).
Proof. exact (MK_COMB (@lem5424833) (@lem5424832 A i s k)). Qed.
Lemma lem5424835 {A : Type'} (i : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term325 A i s k f) = (term326 A i s f k).
Proof. exact (eq_refl (term325 A i s k f)). Qed.
Lemma lem5424836 {A : Type'} (j : type977 A) (f : nat -> A) : (j f) = (j f).
Proof. exact (eq_refl (j f)). Qed.
Lemma lem5424837 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) (j : type977 A) (f : nat -> A) : (term335 A i s k j f) = (term336 A i s k j f).
Proof. exact (MK_COMB (@lem5424835 A i s f k) (@lem5424836 A j f)). Qed.
Lemma lem5424838 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term336 A i s k j f) = (term337 A i j s f k).
Proof. exact (eq_refl (term336 A i s k j f)). Qed.
Lemma lem5424839 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term335 A i s k j f) = (term337 A i j s f k).
Proof. exact (TRANS (@lem5424837 A i s k j f) (@lem5424838 A i j s f k)). Qed.
Lemma lem5424840 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term338 A i s k j) = (term339 A i j s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424839 A i j s f k)). Qed.
Lemma lem5424841 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5424842 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term340 A i s k j) = (term341 A i j s k).
Proof. exact (MK_COMB (@lem5424841 A) (@lem5424840 A i j s k)). Qed.
Lemma lem5424843 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term342 A i s k) = (term343 A i s k).
Proof. exact (fun_ext (fun j : type977 A => @lem5424842 A i j s k)). Qed.
Lemma lem5424844 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5424845 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term323 A i s k) = (term344 A i s k).
Proof. exact (MK_COMB (@lem5424844 A) (@lem5424843 A i s k)). Qed.
Lemma lem5424846 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : ((term322 A i s k) = (term323 A i s k)) = ((term318 A i s k) = (term344 A i s k)).
Proof. exact (MK_COMB (@lem5424834 A i s k) (@lem5424845 A i s k)). Qed.
Lemma lem5424847 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term318 A i s k) = (term344 A i s k).
Proof. exact (EQ_MP (@lem5424846 A i s k) (@lem5424821 A i s k)). Qed.
Lemma lem5424848 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term320 A s k) = (term345 A s k).
Proof. exact (fun_ext (fun i : type977 A => @lem5424847 A i s k)). Qed.
Lemma lem5424849 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5424850 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term321 A s k) = (term346 A s k).
Proof. exact (MK_COMB (@lem5424849 A) (@lem5424848 A s k)). Qed.
Lemma lem5424851 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term296 A s k) = (term346 A s k).
Proof. exact (TRANS (@lem5424817 A s k) (@lem5424850 A s k)). Qed.
Lemma lem5424852 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term202 A s k) = (term346 A s k).
Proof. exact (TRANS (@lem5424787 A s k) (@lem5424851 A s k)). Qed.
Lemma lem5424853 {A : Type'} (s : A -> Prop) : (term212 A s) = (term347 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424852 A s k)). Qed.
Lemma lem5424854 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424855 {A : Type'} (s : A -> Prop) : (term213 A s) = (term348 A s).
Proof. exact (MK_COMB (@lem5424854) (@lem5424853 A s)). Qed.
Lemma lem5424857 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5424858 {A : Type'} (P : type979 A) : (term349 A P) = (term350 A P).
Proof. exact (@lem5424857 (nat -> Prop) (type977 A) P). Qed.
Lemma lem5424859 {A : Type'} (s : A -> Prop) : (term351 A s) = (term352 A s).
Proof. exact (@lem5424858 A (term353 A s)). Qed.
Lemma lem5424860 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term354 A s k) = (term345 A s k).
Proof. exact (eq_refl (term354 A s k)). Qed.
Lemma lem5424861 {A : Type'} (i : type977 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5424862 {A : Type'} (s : A -> Prop) (k : nat -> Prop) (i : type977 A) : (term355 A s k i) = (term356 A s k i).
Proof. exact (MK_COMB (@lem5424860 A s k) (@lem5424861 A i)). Qed.
Lemma lem5424863 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term356 A s k i) = (term344 A i s k).
Proof. exact (eq_refl (term356 A s k i)). Qed.
Lemma lem5424864 {A : Type'} (i : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term355 A s k i) = (term344 A i s k).
Proof. exact (TRANS (@lem5424862 A s k i) (@lem5424863 A i s k)). Qed.
Lemma lem5424865 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term357 A s k) = (term345 A s k).
Proof. exact (fun_ext (fun i : type977 A => @lem5424864 A i s k)). Qed.
Lemma lem5424866 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5424867 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term358 A s k) = (term346 A s k).
Proof. exact (MK_COMB (@lem5424866 A) (@lem5424865 A s k)). Qed.
Lemma lem5424868 {A : Type'} (s : A -> Prop) : (term359 A s) = (term347 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424867 A s k)). Qed.
Lemma lem5424869 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424870 {A : Type'} (s : A -> Prop) : (term351 A s) = (term348 A s).
Proof. exact (MK_COMB (@lem5424869) (@lem5424868 A s)). Qed.
Lemma lem5424871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424872 {A : Type'} (s : A -> Prop) : (term360 A s) = (term361 A s).
Proof. exact (MK_COMB (@lem5424871) (@lem5424870 A s)). Qed.
Lemma lem5424873 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term354 A s k) = (term345 A s k).
Proof. exact (eq_refl (term354 A s k)). Qed.
Lemma lem5424874 {A : Type'} (i : type984 A) (k : nat -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem5424875 {A : Type'} (s : A -> Prop) (i : type984 A) (k : nat -> Prop) : (term362 A s i k) = (term363 A s i k).
Proof. exact (MK_COMB (@lem5424873 A s k) (@lem5424874 A i k)). Qed.
Lemma lem5424876 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term363 A s i k) = (term364 A i s k).
Proof. exact (eq_refl (term363 A s i k)). Qed.
Lemma lem5424877 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term362 A s i k) = (term364 A i s k).
Proof. exact (TRANS (@lem5424875 A s i k) (@lem5424876 A i s k)). Qed.
Lemma lem5424878 {A : Type'} (i : type984 A) (s : A -> Prop) : (term365 A s i) = (term366 A i s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424877 A i s k)). Qed.
Lemma lem5424879 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424880 {A : Type'} (i : type984 A) (s : A -> Prop) : (term367 A s i) = (term368 A i s).
Proof. exact (MK_COMB (@lem5424879) (@lem5424878 A i s)). Qed.
Lemma lem5424881 {A : Type'} (s : A -> Prop) : (term369 A s) = (term370 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5424880 A i s)). Qed.
Lemma lem5424882 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424883 {A : Type'} (s : A -> Prop) : (term352 A s) = (term371 A s).
Proof. exact (MK_COMB (@lem5424882 A) (@lem5424881 A s)). Qed.
Lemma lem5424884 {A : Type'} (s : A -> Prop) : ((term351 A s) = (term352 A s)) = ((term348 A s) = (term371 A s)).
Proof. exact (MK_COMB (@lem5424872 A s) (@lem5424883 A s)). Qed.
Lemma lem5424885 {A : Type'} (s : A -> Prop) : (term348 A s) = (term371 A s).
Proof. exact (EQ_MP (@lem5424884 A s) (@lem5424859 A s)). Qed.
Lemma lem5424887 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5424888 {A : Type'} (P : type979 A) : (term349 A P) = (term350 A P).
Proof. exact (@lem5424887 (nat -> Prop) (type977 A) P). Qed.
Lemma lem5424889 {A : Type'} (i : type984 A) (s : A -> Prop) : (term372 A i s) = (term373 A i s).
Proof. exact (@lem5424888 A (term374 A i s)). Qed.
Lemma lem5424890 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term375 A i s k) = (term376 A i s k).
Proof. exact (eq_refl (term375 A i s k)). Qed.
Lemma lem5424891 {A : Type'} (j : type977 A) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5424892 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) (j : type977 A) : (term377 A i s k j) = (term378 A i s k j).
Proof. exact (MK_COMB (@lem5424890 A i s k) (@lem5424891 A j)). Qed.
Lemma lem5424893 {A : Type'} (i : type984 A) (j : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term378 A i s k j) = (term379 A i j s k).
Proof. exact (eq_refl (term378 A i s k j)). Qed.
Lemma lem5424894 {A : Type'} (i : type984 A) (j : type977 A) (s : A -> Prop) (k : nat -> Prop) : (term377 A i s k j) = (term379 A i j s k).
Proof. exact (TRANS (@lem5424892 A i s k j) (@lem5424893 A i j s k)). Qed.
Lemma lem5424895 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term380 A i s k) = (term376 A i s k).
Proof. exact (fun_ext (fun j : type977 A => @lem5424894 A i j s k)). Qed.
Lemma lem5424896 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5424897 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term381 A i s k) = (term364 A i s k).
Proof. exact (MK_COMB (@lem5424896 A) (@lem5424895 A i s k)). Qed.
Lemma lem5424898 {A : Type'} (i : type984 A) (s : A -> Prop) : (term382 A i s) = (term366 A i s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424897 A i s k)). Qed.
Lemma lem5424899 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424900 {A : Type'} (i : type984 A) (s : A -> Prop) : (term372 A i s) = (term368 A i s).
Proof. exact (MK_COMB (@lem5424899) (@lem5424898 A i s)). Qed.
Lemma lem5424901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424902 {A : Type'} (i : type984 A) (s : A -> Prop) : (term383 A i s) = (term384 A i s).
Proof. exact (MK_COMB (@lem5424901) (@lem5424900 A i s)). Qed.
Lemma lem5424903 {A : Type'} (i : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term375 A i s k) = (term376 A i s k).
Proof. exact (eq_refl (term375 A i s k)). Qed.
Lemma lem5424904 {A : Type'} (j : type984 A) (k : nat -> Prop) : (j k) = (j k).
Proof. exact (eq_refl (j k)). Qed.
Lemma lem5424905 {A : Type'} (i : type984 A) (s : A -> Prop) (j : type984 A) (k : nat -> Prop) : (term385 A i s j k) = (term386 A i s j k).
Proof. exact (MK_COMB (@lem5424903 A i s k) (@lem5424904 A j k)). Qed.
Lemma lem5424906 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term386 A i s j k) = (term387 A i j s k).
Proof. exact (eq_refl (term386 A i s j k)). Qed.
Lemma lem5424907 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term385 A i s j k) = (term387 A i j s k).
Proof. exact (TRANS (@lem5424905 A i s j k) (@lem5424906 A i j s k)). Qed.
Lemma lem5424908 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term388 A i s j) = (term389 A i j s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424907 A i j s k)). Qed.
Lemma lem5424909 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5424910 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term390 A i s j) = (term391 A i j s).
Proof. exact (MK_COMB (@lem5424909) (@lem5424908 A i j s)). Qed.
Lemma lem5424911 {A : Type'} (i : type984 A) (s : A -> Prop) : (term392 A i s) = (term393 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5424910 A i j s)). Qed.
Lemma lem5424912 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424913 {A : Type'} (i : type984 A) (s : A -> Prop) : (term373 A i s) = (term394 A i s).
Proof. exact (MK_COMB (@lem5424912 A) (@lem5424911 A i s)). Qed.
Lemma lem5424914 {A : Type'} (i : type984 A) (s : A -> Prop) : ((term372 A i s) = (term373 A i s)) = ((term368 A i s) = (term394 A i s)).
Proof. exact (MK_COMB (@lem5424902 A i s) (@lem5424913 A i s)). Qed.
Lemma lem5424915 {A : Type'} (i : type984 A) (s : A -> Prop) : (term368 A i s) = (term394 A i s).
Proof. exact (EQ_MP (@lem5424914 A i s) (@lem5424889 A i s)). Qed.
Lemma lem5424916 {A : Type'} (s : A -> Prop) : (term370 A s) = (term395 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5424915 A i s)). Qed.
Lemma lem5424917 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424918 {A : Type'} (s : A -> Prop) : (term371 A s) = (term396 A s).
Proof. exact (MK_COMB (@lem5424917 A) (@lem5424916 A s)). Qed.
Lemma lem5424919 {A : Type'} (s : A -> Prop) : (term348 A s) = (term396 A s).
Proof. exact (TRANS (@lem5424885 A s) (@lem5424918 A s)). Qed.
Lemma lem5424920 {A : Type'} (s : A -> Prop) : (term213 A s) = (term396 A s).
Proof. exact (TRANS (@lem5424855 A s) (@lem5424919 A s)). Qed.
Lemma lem5424921 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424922 {A : Type'} (s : A -> Prop) : (term221 A s) = (term397 A s).
Proof. exact (MK_COMB (@lem5424921 A s) (@lem5424920 A s)). Qed.
Lemma lem5424924 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5424925 {A : Type'} (P : Prop) (Q : type249 A) : (term400 A P Q) = (term401 A P Q).
Proof. exact (@lem5424924 (type984 A) P Q). Qed.
Lemma lem5424926 {A : Type'} (s : A -> Prop) : (term402 A s) = (term403 A s).
Proof. exact (@lem5424925 A (@FINITE A s) (term395 A s)). Qed.
Lemma lem5424927 {A : Type'} (i : type984 A) (s : A -> Prop) : (term404 A s i) = (term394 A i s).
Proof. exact (eq_refl (term404 A s i)). Qed.
Lemma lem5424928 {A : Type'} (s : A -> Prop) : (term405 A s) = (term395 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5424927 A i s)). Qed.
Lemma lem5424929 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424930 {A : Type'} (s : A -> Prop) : (term406 A s) = (term396 A s).
Proof. exact (MK_COMB (@lem5424929 A) (@lem5424928 A s)). Qed.
Lemma lem5424931 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424932 {A : Type'} (s : A -> Prop) : (term402 A s) = (term397 A s).
Proof. exact (MK_COMB (@lem5424931 A s) (@lem5424930 A s)). Qed.
Lemma lem5424933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424934 {A : Type'} (s : A -> Prop) : (term407 A s) = (term408 A s).
Proof. exact (MK_COMB (@lem5424933) (@lem5424932 A s)). Qed.
Lemma lem5424935 {A : Type'} (i : type984 A) (s : A -> Prop) : (term404 A s i) = (term394 A i s).
Proof. exact (eq_refl (term404 A s i)). Qed.
Lemma lem5424936 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424937 {A : Type'} (i : type984 A) (s : A -> Prop) : (term409 A s i) = (term410 A i s).
Proof. exact (MK_COMB (@lem5424936 A s) (@lem5424935 A i s)). Qed.
Lemma lem5424938 {A : Type'} (s : A -> Prop) : (term411 A s) = (term412 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5424937 A i s)). Qed.
Lemma lem5424939 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424940 {A : Type'} (s : A -> Prop) : (term403 A s) = (term413 A s).
Proof. exact (MK_COMB (@lem5424939 A) (@lem5424938 A s)). Qed.
Lemma lem5424941 {A : Type'} (s : A -> Prop) : ((term402 A s) = (term403 A s)) = ((term397 A s) = (term413 A s)).
Proof. exact (MK_COMB (@lem5424934 A s) (@lem5424940 A s)). Qed.
Lemma lem5424942 {A : Type'} (s : A -> Prop) : (term397 A s) = (term413 A s).
Proof. exact (EQ_MP (@lem5424941 A s) (@lem5424926 A s)). Qed.
Lemma lem5424944 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5424945 {A : Type'} (P : Prop) (Q : type249 A) : (term400 A P Q) = (term401 A P Q).
Proof. exact (@lem5424944 (type984 A) P Q). Qed.
Lemma lem5424946 {A : Type'} (i : type984 A) (s : A -> Prop) : (term414 A i s) = (term415 A i s).
Proof. exact (@lem5424945 A (@FINITE A s) (term393 A i s)). Qed.
Lemma lem5424947 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term416 A i s j) = (term391 A i j s).
Proof. exact (eq_refl (term416 A i s j)). Qed.
Lemma lem5424948 {A : Type'} (i : type984 A) (s : A -> Prop) : (term417 A i s) = (term393 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5424947 A i j s)). Qed.
Lemma lem5424949 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424950 {A : Type'} (i : type984 A) (s : A -> Prop) : (term418 A i s) = (term394 A i s).
Proof. exact (MK_COMB (@lem5424949 A) (@lem5424948 A i s)). Qed.
Lemma lem5424951 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424952 {A : Type'} (i : type984 A) (s : A -> Prop) : (term414 A i s) = (term410 A i s).
Proof. exact (MK_COMB (@lem5424951 A s) (@lem5424950 A i s)). Qed.
Lemma lem5424953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424954 {A : Type'} (i : type984 A) (s : A -> Prop) : (term419 A i s) = (term420 A i s).
Proof. exact (MK_COMB (@lem5424953) (@lem5424952 A i s)). Qed.
Lemma lem5424955 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term416 A i s j) = (term391 A i j s).
Proof. exact (eq_refl (term416 A i s j)). Qed.
Lemma lem5424956 {A : Type'} (s : A -> Prop) : (term219 A s) = (term219 A s).
Proof. exact (eq_refl (term219 A s)). Qed.
Lemma lem5424957 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term421 A i s j) = (term422 A i j s).
Proof. exact (MK_COMB (@lem5424956 A s) (@lem5424955 A i j s)). Qed.
Lemma lem5424958 {A : Type'} (i : type984 A) (s : A -> Prop) : (term423 A i s) = (term424 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5424957 A i j s)). Qed.
Lemma lem5424959 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424960 {A : Type'} (i : type984 A) (s : A -> Prop) : (term415 A i s) = (term425 A i s).
Proof. exact (MK_COMB (@lem5424959 A) (@lem5424958 A i s)). Qed.
Lemma lem5424961 {A : Type'} (i : type984 A) (s : A -> Prop) : ((term414 A i s) = (term415 A i s)) = ((term410 A i s) = (term425 A i s)).
Proof. exact (MK_COMB (@lem5424954 A i s) (@lem5424960 A i s)). Qed.
Lemma lem5424962 {A : Type'} (i : type984 A) (s : A -> Prop) : (term410 A i s) = (term425 A i s).
Proof. exact (EQ_MP (@lem5424961 A i s) (@lem5424946 A i s)). Qed.
Lemma lem5424963 {A : Type'} (s : A -> Prop) : (term412 A s) = (term426 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5424962 A i s)). Qed.
Lemma lem5424964 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5424965 {A : Type'} (s : A -> Prop) : (term413 A s) = (term427 A s).
Proof. exact (MK_COMB (@lem5424964 A) (@lem5424963 A s)). Qed.
Lemma lem5424966 {A : Type'} (s : A -> Prop) : (term397 A s) = (term427 A s).
Proof. exact (TRANS (@lem5424942 A s) (@lem5424965 A s)). Qed.
Lemma lem5424967 {A : Type'} (s : A -> Prop) : (term221 A s) = (term427 A s).
Proof. exact (TRANS (@lem5424922 A s) (@lem5424966 A s)). Qed.
Lemma lem5424968 {A : Type'} : (term241 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5424967 A s)). Qed.
Lemma lem5424969 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5424970 {A : Type'} : (term252 A) = (term429 A).
Proof. exact (MK_COMB (@lem5424969 A) (@lem5424968 A)). Qed.
Lemma lem5424971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5424972 {A : Type'} : (term254 A) = (term430 A).
Proof. exact (MK_COMB (@lem5424971) (@lem5424970 A)). Qed.
Lemma lem5424974 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5424975 (P : Prop) (Q : type993) : (term431 P Q) = (term432 P Q).
Proof. exact (@lem5424974 (nat -> Prop) P Q). Qed.
Lemma lem5424976 {A : Type'} (s : A -> Prop) : (term433 A s) = (term434 A s).
Proof. exact (@lem5424975 (term435 A s) (term214 A s)). Qed.
Lemma lem5424977 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term436 A s k) = (term204 A s k).
Proof. exact (eq_refl (term436 A s k)). Qed.
Lemma lem5424978 {A : Type'} (s : A -> Prop) : (term437 A s) = (term214 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424977 A s k)). Qed.
Lemma lem5424979 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5424980 {A : Type'} (s : A -> Prop) : (term438 A s) = (term215 A s).
Proof. exact (MK_COMB (@lem5424979) (@lem5424978 A s)). Qed.
Lemma lem5424981 {A : Type'} (s : A -> Prop) : (term216 A s) = (term216 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem5424982 {A : Type'} (s : A -> Prop) : (term433 A s) = (term218 A s).
Proof. exact (MK_COMB (@lem5424981 A s) (@lem5424980 A s)). Qed.
Lemma lem5424983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5424984 {A : Type'} (s : A -> Prop) : (term439 A s) = (term440 A s).
Proof. exact (MK_COMB (@lem5424983) (@lem5424982 A s)). Qed.
Lemma lem5424985 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term436 A s k) = (term204 A s k).
Proof. exact (eq_refl (term436 A s k)). Qed.
Lemma lem5424986 {A : Type'} (s : A -> Prop) : (term216 A s) = (term216 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem5424987 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term441 A s k) = (term442 A s k).
Proof. exact (MK_COMB (@lem5424986 A s) (@lem5424985 A s k)). Qed.
Lemma lem5424988 {A : Type'} (s : A -> Prop) : (term443 A s) = (term444 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5424987 A s k)). Qed.
Lemma lem5424989 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5424990 {A : Type'} (s : A -> Prop) : (term434 A s) = (term445 A s).
Proof. exact (MK_COMB (@lem5424989) (@lem5424988 A s)). Qed.
Lemma lem5424991 {A : Type'} (s : A -> Prop) : ((term433 A s) = (term434 A s)) = ((term218 A s) = (term445 A s)).
Proof. exact (MK_COMB (@lem5424984 A s) (@lem5424990 A s)). Qed.
Lemma lem5424992 {A : Type'} (s : A -> Prop) : (term218 A s) = (term445 A s).
Proof. exact (EQ_MP (@lem5424991 A s) (@lem5424976 A s)). Qed.
Lemma lem5424994 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5424995 {A : Type'} (P : Prop) (Q : type976 A) : (term446 A P Q) = (term447 A P Q).
Proof. exact (@lem5424994 (nat -> A) P Q). Qed.
Lemma lem5424996 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term448 A s k) = (term449 A s k).
Proof. exact (@lem5424995 A (term435 A s) (term203 A s k)). Qed.
Lemma lem5424997 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term450 A s k f) = (term193 A s f k).
Proof. exact (eq_refl (term450 A s k f)). Qed.
Lemma lem5424998 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term451 A s k) = (term203 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5424997 A s f k)). Qed.
Lemma lem5424999 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5425000 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term452 A s k) = (term204 A s k).
Proof. exact (MK_COMB (@lem5424999 A) (@lem5424998 A s k)). Qed.
Lemma lem5425001 {A : Type'} (s : A -> Prop) : (term216 A s) = (term216 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem5425002 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term448 A s k) = (term442 A s k).
Proof. exact (MK_COMB (@lem5425001 A s) (@lem5425000 A s k)). Qed.
Lemma lem5425003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425004 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term453 A s k) = (term454 A s k).
Proof. exact (MK_COMB (@lem5425003) (@lem5425002 A s k)). Qed.
Lemma lem5425005 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term450 A s k f) = (term193 A s f k).
Proof. exact (eq_refl (term450 A s k f)). Qed.
Lemma lem5425006 {A : Type'} (s : A -> Prop) : (term216 A s) = (term216 A s).
Proof. exact (eq_refl (term216 A s)). Qed.
Lemma lem5425007 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term455 A s k f) = (term456 A s f k).
Proof. exact (MK_COMB (@lem5425006 A s) (@lem5425005 A s f k)). Qed.
Lemma lem5425008 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term457 A s k) = (term458 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425007 A s f k)). Qed.
Lemma lem5425009 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5425010 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term449 A s k) = (term459 A s k).
Proof. exact (MK_COMB (@lem5425009 A) (@lem5425008 A s k)). Qed.
Lemma lem5425011 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : ((term448 A s k) = (term449 A s k)) = ((term442 A s k) = (term459 A s k)).
Proof. exact (MK_COMB (@lem5425004 A s k) (@lem5425010 A s k)). Qed.
Lemma lem5425012 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term442 A s k) = (term459 A s k).
Proof. exact (EQ_MP (@lem5425011 A s k) (@lem5424996 A s k)). Qed.
Lemma lem5425013 {A : Type'} (s : A -> Prop) : (term444 A s) = (term460 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5425012 A s k)). Qed.
Lemma lem5425014 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5425015 {A : Type'} (s : A -> Prop) : (term445 A s) = (term461 A s).
Proof. exact (MK_COMB (@lem5425014) (@lem5425013 A s)). Qed.
Lemma lem5425016 {A : Type'} (s : A -> Prop) : (term218 A s) = (term461 A s).
Proof. exact (TRANS (@lem5424992 A s) (@lem5425015 A s)). Qed.
Lemma lem5425017 {A : Type'} : (term242 A) = (term462 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425016 A s)). Qed.
Lemma lem5425018 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5425019 {A : Type'} : (term257 A) = (term463 A).
Proof. exact (MK_COMB (@lem5425018 A) (@lem5425017 A)). Qed.
Lemma lem5425020 {A : Type'} : (term258 A) = (term464 A).
Proof. exact (MK_COMB (@lem5424972 A) (@lem5425019 A)). Qed.
Lemma lem5425022 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5425023 {A : Type'} (P : type686 A) (Q : type686 A) : (term238 A P Q) = (term237 A P Q).
Proof. exact (@lem5425022 (A -> Prop) P Q). Qed.
Lemma lem5425024 {A : Type'} : (term465 A) = (term466 A).
Proof. exact (@lem5425023 A (term428 A) (term462 A)). Qed.
Lemma lem5425025 {A : Type'} (s : A -> Prop) : (term467 A s) = (term427 A s).
Proof. exact (eq_refl (term467 A s)). Qed.
Lemma lem5425026 {A : Type'} : (term468 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425025 A s)). Qed.
Lemma lem5425027 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5425028 {A : Type'} : (term469 A) = (term429 A).
Proof. exact (MK_COMB (@lem5425027 A) (@lem5425026 A)). Qed.
Lemma lem5425029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425030 {A : Type'} : (term470 A) = (term430 A).
Proof. exact (MK_COMB (@lem5425029) (@lem5425028 A)). Qed.
Lemma lem5425031 {A : Type'} (s : A -> Prop) : (term471 A s) = (term461 A s).
Proof. exact (eq_refl (term471 A s)). Qed.
Lemma lem5425032 {A : Type'} : (term472 A) = (term462 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425031 A s)). Qed.
Lemma lem5425033 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5425034 {A : Type'} : (term473 A) = (term463 A).
Proof. exact (MK_COMB (@lem5425033 A) (@lem5425032 A)). Qed.
Lemma lem5425035 {A : Type'} : (term465 A) = (term464 A).
Proof. exact (MK_COMB (@lem5425030 A) (@lem5425034 A)). Qed.
Lemma lem5425036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425037 {A : Type'} : (term474 A) = (term475 A).
Proof. exact (MK_COMB (@lem5425036) (@lem5425035 A)). Qed.
Lemma lem5425038 {A : Type'} (s : A -> Prop) : (term467 A s) = (term427 A s).
Proof. exact (eq_refl (term467 A s)). Qed.
Lemma lem5425039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425040 {A : Type'} (s : A -> Prop) : (term476 A s) = (term477 A s).
Proof. exact (MK_COMB (@lem5425039) (@lem5425038 A s)). Qed.
Lemma lem5425041 {A : Type'} (s : A -> Prop) : (term471 A s) = (term461 A s).
Proof. exact (eq_refl (term471 A s)). Qed.
Lemma lem5425042 {A : Type'} (s : A -> Prop) : (term478 A s) = (term479 A s).
Proof. exact (MK_COMB (@lem5425040 A s) (@lem5425041 A s)). Qed.
Lemma lem5425043 {A : Type'} : (term480 A) = (term481 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425042 A s)). Qed.
Lemma lem5425044 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5425045 {A : Type'} : (term466 A) = (term482 A).
Proof. exact (MK_COMB (@lem5425044 A) (@lem5425043 A)). Qed.
Lemma lem5425046 {A : Type'} : ((term465 A) = (term466 A)) = ((term464 A) = (term482 A)).
Proof. exact (MK_COMB (@lem5425037 A) (@lem5425045 A)). Qed.
Lemma lem5425047 {A : Type'} : (term464 A) = (term482 A).
Proof. exact (EQ_MP (@lem5425046 A) (@lem5425024 A)). Qed.
Lemma lem5425051 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5425052 {A : Type'} (P : type249 A) (Q : Prop) : (term483 A P Q) = (term484 A P Q).
Proof. exact (@lem5425051 (type984 A) P Q). Qed.
Lemma lem5425053 {A : Type'} (s : A -> Prop) : (term485 A s) = (term486 A s).
Proof. exact (@lem5425052 A (term426 A s) (term461 A s)). Qed.
Lemma lem5425054 {A : Type'} (i : type984 A) (s : A -> Prop) : (term487 A s i) = (term425 A i s).
Proof. exact (eq_refl (term487 A s i)). Qed.
Lemma lem5425055 {A : Type'} (s : A -> Prop) : (term488 A s) = (term426 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5425054 A i s)). Qed.
Lemma lem5425056 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425057 {A : Type'} (s : A -> Prop) : (term489 A s) = (term427 A s).
Proof. exact (MK_COMB (@lem5425056 A) (@lem5425055 A s)). Qed.
Lemma lem5425058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425059 {A : Type'} (s : A -> Prop) : (term490 A s) = (term477 A s).
Proof. exact (MK_COMB (@lem5425058) (@lem5425057 A s)). Qed.
Lemma lem5425060 {A : Type'} (s : A -> Prop) : (term461 A s) = (term461 A s).
Proof. exact (eq_refl (term461 A s)). Qed.
Lemma lem5425061 {A : Type'} (s : A -> Prop) : (term485 A s) = (term479 A s).
Proof. exact (MK_COMB (@lem5425059 A s) (@lem5425060 A s)). Qed.
Lemma lem5425062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425063 {A : Type'} (s : A -> Prop) : (term491 A s) = (term492 A s).
Proof. exact (MK_COMB (@lem5425062) (@lem5425061 A s)). Qed.
Lemma lem5425064 {A : Type'} (i : type984 A) (s : A -> Prop) : (term487 A s i) = (term425 A i s).
Proof. exact (eq_refl (term487 A s i)). Qed.
Lemma lem5425065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425066 {A : Type'} (i : type984 A) (s : A -> Prop) : (term493 A s i) = (term494 A i s).
Proof. exact (MK_COMB (@lem5425065) (@lem5425064 A i s)). Qed.
Lemma lem5425067 {A : Type'} (s : A -> Prop) : (term461 A s) = (term461 A s).
Proof. exact (eq_refl (term461 A s)). Qed.
Lemma lem5425068 {A : Type'} (i : type984 A) (s : A -> Prop) : (term495 A i s) = (term496 A i s).
Proof. exact (MK_COMB (@lem5425066 A i s) (@lem5425067 A s)). Qed.
Lemma lem5425069 {A : Type'} (s : A -> Prop) : (term497 A s) = (term498 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5425068 A i s)). Qed.
Lemma lem5425070 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425071 {A : Type'} (s : A -> Prop) : (term486 A s) = (term499 A s).
Proof. exact (MK_COMB (@lem5425070 A) (@lem5425069 A s)). Qed.
Lemma lem5425072 {A : Type'} (s : A -> Prop) : ((term485 A s) = (term486 A s)) = ((term479 A s) = (term499 A s)).
Proof. exact (MK_COMB (@lem5425063 A s) (@lem5425071 A s)). Qed.
Lemma lem5425073 {A : Type'} (s : A -> Prop) : (term479 A s) = (term499 A s).
Proof. exact (EQ_MP (@lem5425072 A s) (@lem5425053 A s)). Qed.
Lemma lem5425077 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5425078 {A : Type'} (P : type249 A) (Q : Prop) : (term483 A P Q) = (term484 A P Q).
Proof. exact (@lem5425077 (type984 A) P Q). Qed.
Lemma lem5425079 {A : Type'} (i : type984 A) (s : A -> Prop) : (term500 A i s) = (term501 A i s).
Proof. exact (@lem5425078 A (term424 A i s) (term461 A s)). Qed.
Lemma lem5425080 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term502 A i s j) = (term422 A i j s).
Proof. exact (eq_refl (term502 A i s j)). Qed.
Lemma lem5425081 {A : Type'} (i : type984 A) (s : A -> Prop) : (term503 A i s) = (term424 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5425080 A i j s)). Qed.
Lemma lem5425082 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425083 {A : Type'} (i : type984 A) (s : A -> Prop) : (term504 A i s) = (term425 A i s).
Proof. exact (MK_COMB (@lem5425082 A) (@lem5425081 A i s)). Qed.
Lemma lem5425084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425085 {A : Type'} (i : type984 A) (s : A -> Prop) : (term505 A i s) = (term494 A i s).
Proof. exact (MK_COMB (@lem5425084) (@lem5425083 A i s)). Qed.
Lemma lem5425086 {A : Type'} (s : A -> Prop) : (term461 A s) = (term461 A s).
Proof. exact (eq_refl (term461 A s)). Qed.
Lemma lem5425087 {A : Type'} (i : type984 A) (s : A -> Prop) : (term500 A i s) = (term496 A i s).
Proof. exact (MK_COMB (@lem5425085 A i s) (@lem5425086 A s)). Qed.
Lemma lem5425088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425089 {A : Type'} (i : type984 A) (s : A -> Prop) : (term506 A i s) = (term507 A i s).
Proof. exact (MK_COMB (@lem5425088) (@lem5425087 A i s)). Qed.
Lemma lem5425090 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term502 A i s j) = (term422 A i j s).
Proof. exact (eq_refl (term502 A i s j)). Qed.
Lemma lem5425091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425092 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term508 A i s j) = (term509 A i j s).
Proof. exact (MK_COMB (@lem5425091) (@lem5425090 A i j s)). Qed.
Lemma lem5425093 {A : Type'} (s : A -> Prop) : (term461 A s) = (term461 A s).
Proof. exact (eq_refl (term461 A s)). Qed.
Lemma lem5425094 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term510 A i j s) = (term511 A i j s).
Proof. exact (MK_COMB (@lem5425092 A i j s) (@lem5425093 A s)). Qed.
Lemma lem5425095 {A : Type'} (i : type984 A) (s : A -> Prop) : (term512 A i s) = (term513 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5425094 A i j s)). Qed.
Lemma lem5425096 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425097 {A : Type'} (i : type984 A) (s : A -> Prop) : (term501 A i s) = (term514 A i s).
Proof. exact (MK_COMB (@lem5425096 A) (@lem5425095 A i s)). Qed.
Lemma lem5425098 {A : Type'} (i : type984 A) (s : A -> Prop) : ((term500 A i s) = (term501 A i s)) = ((term496 A i s) = (term514 A i s)).
Proof. exact (MK_COMB (@lem5425089 A i s) (@lem5425097 A i s)). Qed.
Lemma lem5425099 {A : Type'} (i : type984 A) (s : A -> Prop) : (term496 A i s) = (term514 A i s).
Proof. exact (EQ_MP (@lem5425098 A i s) (@lem5425079 A i s)). Qed.
Lemma lem5425101 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5425102 (P : Prop) (Q : type993) : (term517 P Q) = (term518 P Q).
Proof. exact (@lem5425101 (nat -> Prop) P Q). Qed.
Lemma lem5425103 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term519 A i j s) = (term520 A i j s).
Proof. exact (@lem5425102 (term422 A i j s) (term460 A s)). Qed.
Lemma lem5425104 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term521 A s k) = (term459 A s k).
Proof. exact (eq_refl (term521 A s k)). Qed.
Lemma lem5425105 {A : Type'} (s : A -> Prop) : (term522 A s) = (term460 A s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5425104 A s k)). Qed.
Lemma lem5425106 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5425107 {A : Type'} (s : A -> Prop) : (term523 A s) = (term461 A s).
Proof. exact (MK_COMB (@lem5425106) (@lem5425105 A s)). Qed.
Lemma lem5425108 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term509 A i j s) = (term509 A i j s).
Proof. exact (eq_refl (term509 A i j s)). Qed.
Lemma lem5425109 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term519 A i j s) = (term511 A i j s).
Proof. exact (MK_COMB (@lem5425108 A i j s) (@lem5425107 A s)). Qed.
Lemma lem5425110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425111 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term524 A i j s) = (term525 A i j s).
Proof. exact (MK_COMB (@lem5425110) (@lem5425109 A i j s)). Qed.
Lemma lem5425112 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term521 A s k) = (term459 A s k).
Proof. exact (eq_refl (term521 A s k)). Qed.
Lemma lem5425113 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term509 A i j s) = (term509 A i j s).
Proof. exact (eq_refl (term509 A i j s)). Qed.
Lemma lem5425114 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term526 A i j s k) = (term527 A i j s k).
Proof. exact (MK_COMB (@lem5425113 A i j s) (@lem5425112 A s k)). Qed.
Lemma lem5425115 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term528 A i j s) = (term529 A i j s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5425114 A i j s k)). Qed.
Lemma lem5425116 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5425117 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term520 A i j s) = (term530 A i j s).
Proof. exact (MK_COMB (@lem5425116) (@lem5425115 A i j s)). Qed.
Lemma lem5425118 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : ((term519 A i j s) = (term520 A i j s)) = ((term511 A i j s) = (term530 A i j s)).
Proof. exact (MK_COMB (@lem5425111 A i j s) (@lem5425117 A i j s)). Qed.
Lemma lem5425119 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term511 A i j s) = (term530 A i j s).
Proof. exact (EQ_MP (@lem5425118 A i j s) (@lem5425103 A i j s)). Qed.
Lemma lem5425121 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5425122 {A : Type'} (P : Prop) (Q : type976 A) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem5425121 (nat -> A) P Q). Qed.
Lemma lem5425123 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term533 A i j s k) = (term534 A i j s k).
Proof. exact (@lem5425122 A (term422 A i j s) (term458 A s k)). Qed.
Lemma lem5425124 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term535 A s k f) = (term456 A s f k).
Proof. exact (eq_refl (term535 A s k f)). Qed.
Lemma lem5425125 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term536 A s k) = (term458 A s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425124 A s f k)). Qed.
Lemma lem5425126 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5425127 {A : Type'} (s : A -> Prop) (k : nat -> Prop) : (term537 A s k) = (term459 A s k).
Proof. exact (MK_COMB (@lem5425126 A) (@lem5425125 A s k)). Qed.
Lemma lem5425128 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term509 A i j s) = (term509 A i j s).
Proof. exact (eq_refl (term509 A i j s)). Qed.
Lemma lem5425129 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term533 A i j s k) = (term527 A i j s k).
Proof. exact (MK_COMB (@lem5425128 A i j s) (@lem5425127 A s k)). Qed.
Lemma lem5425130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425131 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term538 A i j s k) = (term539 A i j s k).
Proof. exact (MK_COMB (@lem5425130) (@lem5425129 A i j s k)). Qed.
Lemma lem5425132 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term535 A s k f) = (term456 A s f k).
Proof. exact (eq_refl (term535 A s k f)). Qed.
Lemma lem5425133 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term509 A i j s) = (term509 A i j s).
Proof. exact (eq_refl (term509 A i j s)). Qed.
Lemma lem5425134 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term540 A i j s k f) = (term541 A i j s f k).
Proof. exact (MK_COMB (@lem5425133 A i j s) (@lem5425132 A s f k)). Qed.
Lemma lem5425135 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term542 A i j s k) = (term543 A i j s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425134 A i j s f k)). Qed.
Lemma lem5425136 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5425137 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term534 A i j s k) = (term544 A i j s k).
Proof. exact (MK_COMB (@lem5425136 A) (@lem5425135 A i j s k)). Qed.
Lemma lem5425138 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : ((term533 A i j s k) = (term534 A i j s k)) = ((term527 A i j s k) = (term544 A i j s k)).
Proof. exact (MK_COMB (@lem5425131 A i j s k) (@lem5425137 A i j s k)). Qed.
Lemma lem5425139 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term527 A i j s k) = (term544 A i j s k).
Proof. exact (EQ_MP (@lem5425138 A i j s k) (@lem5425123 A i j s k)). Qed.
Lemma lem5425140 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term529 A i j s) = (term545 A i j s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5425139 A i j s k)). Qed.
Lemma lem5425141 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5425142 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term530 A i j s) = (term546 A i j s).
Proof. exact (MK_COMB (@lem5425141) (@lem5425140 A i j s)). Qed.
Lemma lem5425143 {A : Type'} (i : type984 A) (j : type984 A) (s : A -> Prop) : (term511 A i j s) = (term546 A i j s).
Proof. exact (TRANS (@lem5425119 A i j s) (@lem5425142 A i j s)). Qed.
Lemma lem5425144 {A : Type'} (i : type984 A) (s : A -> Prop) : (term513 A i s) = (term547 A i s).
Proof. exact (fun_ext (fun j : type984 A => @lem5425143 A i j s)). Qed.
Lemma lem5425145 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425146 {A : Type'} (i : type984 A) (s : A -> Prop) : (term514 A i s) = (term548 A i s).
Proof. exact (MK_COMB (@lem5425145 A) (@lem5425144 A i s)). Qed.
Lemma lem5425147 {A : Type'} (i : type984 A) (s : A -> Prop) : (term496 A i s) = (term548 A i s).
Proof. exact (TRANS (@lem5425099 A i s) (@lem5425146 A i s)). Qed.
Lemma lem5425148 {A : Type'} (s : A -> Prop) : (term498 A s) = (term549 A s).
Proof. exact (fun_ext (fun i : type984 A => @lem5425147 A i s)). Qed.
Lemma lem5425149 {A : Type'} : (@ex ((nat -> Prop) -> (nat -> A) -> nat)) = (@ex ((nat -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5425150 {A : Type'} (s : A -> Prop) : (term499 A s) = (term550 A s).
Proof. exact (MK_COMB (@lem5425149 A) (@lem5425148 A s)). Qed.
Lemma lem5425151 {A : Type'} (s : A -> Prop) : (term479 A s) = (term550 A s).
Proof. exact (TRANS (@lem5425073 A s) (@lem5425150 A s)). Qed.
Lemma lem5425152 {A : Type'} : (term481 A) = (term551 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425151 A s)). Qed.
Lemma lem5425153 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5425154 {A : Type'} : (term482 A) = (term552 A).
Proof. exact (MK_COMB (@lem5425153 A) (@lem5425152 A)). Qed.
Lemma lem5425155 {A : Type'} : (term464 A) = (term552 A).
Proof. exact (TRANS (@lem5425047 A) (@lem5425154 A)). Qed.
Lemma lem5425156 {A : Type'} : (term258 A) = (term552 A).
Proof. exact (TRANS (@lem5425020 A) (@lem5425155 A)). Qed.
Lemma lem5425157 {A : Type'} : (term234 A) = (term552 A).
Proof. exact (TRANS (@lem5424448 A) (@lem5425156 A)). Qed.
Lemma lem5425158 {A : Type'} : (term10 A) = (term552 A).
Proof. exact (TRANS (@lem5424421 A) (@lem5425157 A)). Qed.
Lemma lem5425159 {A : Type'} (h1 : term10 A) : term552 A.
Proof. exact (EQ_MP (@lem5425158 A) (@lem5424279 A h1)). Qed.
Lemma lem5425516 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term114 A f s) = (term553 A f s).
Proof. exact (@lem17265 (@FINITE nat s) (term554 A f s)). Qed.
Lemma lem5425517 {A : Type'} (f : nat -> A) : (term115 A f) = (term555 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5425516 A f s)). Qed.
Lemma lem5425518 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5425519 {A : Type'} (f : nat -> A) : (term116 A f) = (term556 A f).
Proof. exact (MK_COMB (@lem5425518) (@lem5425517 A f)). Qed.
Lemma lem5425520 {A : Type'} : (term117 A) = (term557 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425519 A f)). Qed.
Lemma lem5425521 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5425578 {A : Type'} : (term15 A) = (term558 A).
Proof. exact (MK_COMB (@lem5425521 A) (@lem5425520 A)). Qed.
Lemma lem5425579 {A : Type'} (h1 : term15 A) : term558 A.
Proof. exact (EQ_MP (@lem5425578 A) (@lem5424285 A h1)). Qed.
Lemma lem5425790 (m : nat) (n : nat) : (term101 m n) = (term101 m n).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem5425791 (m : nat) : (term102 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem5425790 m n)). Qed.
Lemma lem5425792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5425793 (m : nat) : (term103 m) = (term103 m).
Proof. exact (MK_COMB (@lem5425792) (@lem5425791 m)). Qed.
Lemma lem5425794 : term104 = term104.
Proof. exact (fun_ext (fun m : nat => @lem5425793 m)). Qed.
Lemma lem5425795 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5425808 : term105 = term105.
Proof. exact (MK_COMB (@lem5425795) (@lem5425794)). Qed.
Lemma lem5425809 (h1 : term105) : term105.
Proof. exact (EQ_MP (@lem5425808) (@lem5424289 h1)). Qed.
Lemma lem5425822 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term559 A s i f j) = (term560 A s i f j).
Proof. exact (@lem17045 (term561 A j s) ((f i) = (f j))). Qed.
Lemma lem5425827 {A : Type'} (i : nat) (s : A -> Prop) : (term562 A i s) = (term562 A i s).
Proof. exact (eq_refl (term562 A i s)). Qed.
Lemma lem5425828 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term563 A s i f j) = (term564 A s i f j).
Proof. exact (MK_COMB (@lem5425827 A i s) (@lem5425822 A s i f j)). Qed.
Lemma lem5425829 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term565 A s i f j) = (term563 A s i f j).
Proof. exact (@lem17045 (term561 A i s) (term566 A s i f j)). Qed.
Lemma lem5425830 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term565 A s i f j) = (term564 A s i f j).
Proof. exact (TRANS (@lem5425829 A s i f j) (@lem5425828 A s i f j)). Qed.
Lemma lem5425835 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5425840 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term567 A s f i j) = (term568 A s f i j).
Proof. exact (@lem17362 (term569 A s i f j) (i = j)). Qed.
Lemma lem5425841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425842 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term570 A s i f j) = (term571 A s i f j).
Proof. exact (MK_COMB (@lem5425841) (@lem5425830 A s i f j)). Qed.
Lemma lem5425843 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term572 A s f i j) = (term573 A s f i j).
Proof. exact (MK_COMB (@lem5425842 A s i f j) (@lem5425835 i j)). Qed.
Lemma lem5425844 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term90 A s f i j) = (term572 A s f i j).
Proof. exact (@lem17265 (term569 A s i f j) (i = j)). Qed.
Lemma lem5425845 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term90 A s f i j) = (term573 A s f i j).
Proof. exact (TRANS (@lem5425844 A s f i j) (@lem5425843 A s f i j)). Qed.
Lemma lem5425846 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5425847 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term574 A s f i) = (term575 A s f i).
Proof. exact (@lem5425846 (term91 A s f i)). Qed.
Lemma lem5425848 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term576 A s f i j) = (term90 A s f i j).
Proof. exact (eq_refl (term576 A s f i j)). Qed.
Lemma lem5425849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5425850 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term577 A s f i j) = (term567 A s f i j).
Proof. exact (MK_COMB (@lem5425849) (@lem5425848 A s f i j)). Qed.
Lemma lem5425851 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term577 A s f i j) = (term568 A s f i j).
Proof. exact (TRANS (@lem5425850 A s f i j) (@lem5425840 A s f i j)). Qed.
Lemma lem5425852 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term578 A s f i) = (term579 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5425851 A s f i j)). Qed.
Lemma lem5425853 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5425854 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term575 A s f i) = (term580 A s f i).
Proof. exact (MK_COMB (@lem5425853) (@lem5425852 A s f i)). Qed.
Lemma lem5425855 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term574 A s f i) = (term580 A s f i).
Proof. exact (TRANS (@lem5425847 A s f i) (@lem5425854 A s f i)). Qed.
Lemma lem5425856 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term91 A s f i) = (term581 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5425845 A s f i j)). Qed.
Lemma lem5425857 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5425858 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term92 A s f i) = (term582 A s f i).
Proof. exact (MK_COMB (@lem5425857) (@lem5425856 A s f i)). Qed.
Lemma lem5425859 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5425860 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term583 A s f) = (term584 A s f).
Proof. exact (@lem5425859 (term93 A s f)). Qed.
Lemma lem5425861 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term585 A s f i) = (term92 A s f i).
Proof. exact (eq_refl (term585 A s f i)). Qed.
Lemma lem5425862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5425863 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term586 A s f i) = (term574 A s f i).
Proof. exact (MK_COMB (@lem5425862) (@lem5425861 A s f i)). Qed.
Lemma lem5425864 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term586 A s f i) = (term580 A s f i).
Proof. exact (TRANS (@lem5425863 A s f i) (@lem5425855 A s f i)). Qed.
Lemma lem5425865 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term587 A s f) = (term588 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5425864 A s f i)). Qed.
Lemma lem5425866 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5425867 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term584 A s f) = (term589 A s f).
Proof. exact (MK_COMB (@lem5425866) (@lem5425865 A s f)). Qed.
Lemma lem5425868 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term583 A s f) = (term589 A s f).
Proof. exact (TRANS (@lem5425860 A s f) (@lem5425867 A s f)). Qed.
Lemma lem5425869 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term93 A s f) = (term590 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5425858 A s f i)). Qed.
Lemma lem5425870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5425871 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term94 A s f) = (term591 A s f).
Proof. exact (MK_COMB (@lem5425870) (@lem5425869 A s f)). Qed.
Lemma lem5425872 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term592 A f s).
Proof. exact (eq_refl (term592 A f s)). Qed.
Lemma lem5425873 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term89 A f s)) = (s = (term89 A f s)).
Proof. exact (eq_refl (s = (term89 A f s))). Qed.
Lemma lem5425874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5425875 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term593 A s f) = (term594 A s f).
Proof. exact (MK_COMB (@lem5425874) (@lem5425868 A s f)). Qed.
Lemma lem5425876 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term595 A f s) = (term596 A f s).
Proof. exact (MK_COMB (@lem5425875 A s f) (@lem5425872 A f s)). Qed.
Lemma lem5425877 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term597 A f s) = (term595 A f s).
Proof. exact (@lem17045 (term94 A s f) (s = (term89 A f s))). Qed.
Lemma lem5425878 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term597 A f s) = (term596 A f s).
Proof. exact (TRANS (@lem5425877 A f s) (@lem5425876 A f s)). Qed.
Lemma lem5425879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5425880 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term95 A s f) = (term598 A s f).
Proof. exact (MK_COMB (@lem5425879) (@lem5425871 A s f)). Qed.
Lemma lem5425881 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term96 A f s) = (term599 A f s).
Proof. exact (MK_COMB (@lem5425880 A s f) (@lem5425873 A f s)). Qed.
Lemma lem5425882 {A : Type'} (P : type976 A) : (term194 A P) = (term195 A P).
Proof. exact (@lem18394 (nat -> A) P). Qed.
Lemma lem5425883 {A : Type'} (s : A -> Prop) : (term600 A s) = (term601 A s).
Proof. exact (@lem5425882 A (term97 A s)). Qed.
Lemma lem5425884 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term602 A s f) = (term96 A f s).
Proof. exact (eq_refl (term602 A s f)). Qed.
Lemma lem5425885 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5425886 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term603 A s f) = (term597 A f s).
Proof. exact (MK_COMB (@lem5425885) (@lem5425884 A f s)). Qed.
Lemma lem5425887 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term603 A s f) = (term596 A f s).
Proof. exact (TRANS (@lem5425886 A f s) (@lem5425878 A f s)). Qed.
Lemma lem5425888 {A : Type'} (s : A -> Prop) : (term604 A s) = (term605 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425887 A f s)). Qed.
Lemma lem5425889 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5425890 {A : Type'} (s : A -> Prop) : (term601 A s) = (term606 A s).
Proof. exact (MK_COMB (@lem5425889 A) (@lem5425888 A s)). Qed.
Lemma lem5425891 {A : Type'} (s : A -> Prop) : (term600 A s) = (term606 A s).
Proof. exact (TRANS (@lem5425883 A s) (@lem5425890 A s)). Qed.
Lemma lem5425892 {A : Type'} (s : A -> Prop) : (term97 A s) = (term607 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5425881 A f s)). Qed.
Lemma lem5425893 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5425894 {A : Type'} (s : A -> Prop) : (term98 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem5425893 A) (@lem5425892 A s)). Qed.
Lemma lem5425896 {A : Type'} (s : A -> Prop) : (term609 A s) = (term609 A s).
Proof. exact (eq_refl (term609 A s)). Qed.
Lemma lem5425897 {A : Type'} (s : A -> Prop) : (term610 A s) = (term611 A s).
Proof. exact (MK_COMB (@lem5425896 A s) (@lem5425894 A s)). Qed.
Lemma lem5425899 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5425900 {A : Type'} (s : A -> Prop) : (term613 A s) = (term614 A s).
Proof. exact (MK_COMB (@lem5425899 A s) (@lem5425891 A s)). Qed.
Lemma lem5425901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5425902 {A : Type'} (s : A -> Prop) : (term615 A s) = (term616 A s).
Proof. exact (MK_COMB (@lem5425901) (@lem5425900 A s)). Qed.
Lemma lem5425903 {A : Type'} (s : A -> Prop) : (term617 A s) = (term618 A s).
Proof. exact (MK_COMB (@lem5425902 A s) (@lem5425897 A s)). Qed.
Lemma lem5425904 {A : Type'} (s : A -> Prop) : ((@FINITE A s) = (term98 A s)) = (term617 A s).
Proof. exact (@lem17784 (@FINITE A s) (term98 A s)). Qed.
Lemma lem5425905 {A : Type'} (s : A -> Prop) : ((@FINITE A s) = (term98 A s)) = (term618 A s).
Proof. exact (TRANS (@lem5425904 A s) (@lem5425903 A s)). Qed.
Lemma lem5425906 {A : Type'} : (term100 A) = (term619 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425905 A s)). Qed.
Lemma lem5425907 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5425908 {A : Type'} : (term11 A) = (term620 A).
Proof. exact (MK_COMB (@lem5425907 A) (@lem5425906 A)). Qed.
Lemma lem5425910 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5425911 {A : Type'} (P : type686 A) (Q : type686 A) : (term623 A P Q) = (term624 A P Q).
Proof. exact (@lem5425910 (A -> Prop) P Q). Qed.
Lemma lem5425912 {A : Type'} : (term625 A) = (term626 A).
Proof. exact (@lem5425911 A (term627 A) (term628 A)). Qed.
Lemma lem5425913 {A : Type'} (s : A -> Prop) : (term629 A s) = (term614 A s).
Proof. exact (eq_refl (term629 A s)). Qed.
Lemma lem5425914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5425915 {A : Type'} (s : A -> Prop) : (term630 A s) = (term616 A s).
Proof. exact (MK_COMB (@lem5425914) (@lem5425913 A s)). Qed.
Lemma lem5425916 {A : Type'} (s : A -> Prop) : (term631 A s) = (term611 A s).
Proof. exact (eq_refl (term631 A s)). Qed.
Lemma lem5425917 {A : Type'} (s : A -> Prop) : (term632 A s) = (term618 A s).
Proof. exact (MK_COMB (@lem5425915 A s) (@lem5425916 A s)). Qed.
Lemma lem5425918 {A : Type'} : (term633 A) = (term619 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425917 A s)). Qed.
Lemma lem5425919 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5425920 {A : Type'} : (term625 A) = (term620 A).
Proof. exact (MK_COMB (@lem5425919 A) (@lem5425918 A)). Qed.
Lemma lem5425921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5425922 {A : Type'} : (term634 A) = (term635 A).
Proof. exact (MK_COMB (@lem5425921) (@lem5425920 A)). Qed.
Lemma lem5425923 {A : Type'} (s : A -> Prop) : (term629 A s) = (term614 A s).
Proof. exact (eq_refl (term629 A s)). Qed.
Lemma lem5425924 {A : Type'} : (term636 A) = (term627 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425923 A s)). Qed.
Lemma lem5425925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5425926 {A : Type'} : (term637 A) = (term638 A).
Proof. exact (MK_COMB (@lem5425925 A) (@lem5425924 A)). Qed.
Lemma lem5425927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5425928 {A : Type'} : (term639 A) = (term640 A).
Proof. exact (MK_COMB (@lem5425927) (@lem5425926 A)). Qed.
Lemma lem5425929 {A : Type'} (s : A -> Prop) : (term631 A s) = (term611 A s).
Proof. exact (eq_refl (term631 A s)). Qed.
Lemma lem5425930 {A : Type'} : (term641 A) = (term628 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5425929 A s)). Qed.
Lemma lem5425931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5425932 {A : Type'} : (term642 A) = (term643 A).
Proof. exact (MK_COMB (@lem5425931 A) (@lem5425930 A)). Qed.
Lemma lem5425933 {A : Type'} : (term626 A) = (term644 A).
Proof. exact (MK_COMB (@lem5425928 A) (@lem5425932 A)). Qed.
Lemma lem5425934 {A : Type'} : ((term625 A) = (term626 A)) = ((term620 A) = (term644 A)).
Proof. exact (MK_COMB (@lem5425922 A) (@lem5425933 A)). Qed.
Lemma lem5425935 {A : Type'} : (term620 A) = (term644 A).
Proof. exact (EQ_MP (@lem5425934 A) (@lem5425912 A)). Qed.
Lemma lem5426213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5426214 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5426213 nat P Q). Qed.
Lemma lem5426215 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term645 A f s) = (term646 A f s).
Proof. exact (@lem5426214 (term588 A s f) (term592 A f s)). Qed.
Lemma lem5426216 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term647 A s f i) = (term580 A s f i).
Proof. exact (eq_refl (term647 A s f i)). Qed.
Lemma lem5426217 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term648 A s f) = (term588 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5426216 A s f i)). Qed.
Lemma lem5426218 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426219 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term649 A s f) = (term589 A s f).
Proof. exact (MK_COMB (@lem5426218) (@lem5426217 A s f)). Qed.
Lemma lem5426220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426221 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term650 A s f) = (term594 A s f).
Proof. exact (MK_COMB (@lem5426220) (@lem5426219 A s f)). Qed.
Lemma lem5426222 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term592 A f s).
Proof. exact (eq_refl (term592 A f s)). Qed.
Lemma lem5426223 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term645 A f s) = (term596 A f s).
Proof. exact (MK_COMB (@lem5426221 A s f) (@lem5426222 A f s)). Qed.
Lemma lem5426224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426225 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term651 A f s) = (term652 A f s).
Proof. exact (MK_COMB (@lem5426224) (@lem5426223 A f s)). Qed.
Lemma lem5426226 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term647 A s f i) = (term580 A s f i).
Proof. exact (eq_refl (term647 A s f i)). Qed.
Lemma lem5426227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426228 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term653 A s f i) = (term654 A s f i).
Proof. exact (MK_COMB (@lem5426227) (@lem5426226 A s f i)). Qed.
Lemma lem5426229 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term592 A f s).
Proof. exact (eq_refl (term592 A f s)). Qed.
Lemma lem5426230 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term655 A i f s) = (term656 A i f s).
Proof. exact (MK_COMB (@lem5426228 A s f i) (@lem5426229 A f s)). Qed.
Lemma lem5426231 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term657 A f s) = (term658 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5426230 A i f s)). Qed.
Lemma lem5426232 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426233 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term646 A f s) = (term659 A f s).
Proof. exact (MK_COMB (@lem5426232) (@lem5426231 A f s)). Qed.
Lemma lem5426234 {A : Type'} (f : nat -> A) (s : A -> Prop) : ((term645 A f s) = (term646 A f s)) = ((term596 A f s) = (term659 A f s)).
Proof. exact (MK_COMB (@lem5426225 A f s) (@lem5426233 A f s)). Qed.
Lemma lem5426235 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term596 A f s) = (term659 A f s).
Proof. exact (EQ_MP (@lem5426234 A f s) (@lem5426215 A f s)). Qed.
Lemma lem5426237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5426238 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5426237 nat P Q). Qed.
Lemma lem5426239 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term660 A i f s) = (term661 A i f s).
Proof. exact (@lem5426238 (term579 A s f i) (term592 A f s)). Qed.
Lemma lem5426240 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term662 A s f i j) = (term568 A s f i j).
Proof. exact (eq_refl (term662 A s f i j)). Qed.
Lemma lem5426241 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term663 A s f i) = (term579 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5426240 A s f i j)). Qed.
Lemma lem5426242 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426243 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term664 A s f i) = (term580 A s f i).
Proof. exact (MK_COMB (@lem5426242) (@lem5426241 A s f i)). Qed.
Lemma lem5426244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426245 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term665 A s f i) = (term654 A s f i).
Proof. exact (MK_COMB (@lem5426244) (@lem5426243 A s f i)). Qed.
Lemma lem5426246 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term592 A f s).
Proof. exact (eq_refl (term592 A f s)). Qed.
Lemma lem5426247 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term660 A i f s) = (term656 A i f s).
Proof. exact (MK_COMB (@lem5426245 A s f i) (@lem5426246 A f s)). Qed.
Lemma lem5426248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426249 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term666 A i f s) = (term667 A i f s).
Proof. exact (MK_COMB (@lem5426248) (@lem5426247 A i f s)). Qed.
Lemma lem5426250 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term662 A s f i j) = (term568 A s f i j).
Proof. exact (eq_refl (term662 A s f i j)). Qed.
Lemma lem5426251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426252 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term668 A s f i j) = (term669 A s f i j).
Proof. exact (MK_COMB (@lem5426251) (@lem5426250 A s f i j)). Qed.
Lemma lem5426253 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term592 A f s).
Proof. exact (eq_refl (term592 A f s)). Qed.
Lemma lem5426254 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term670 A i j f s) = (term671 A i j f s).
Proof. exact (MK_COMB (@lem5426252 A s f i j) (@lem5426253 A f s)). Qed.
Lemma lem5426255 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term672 A i f s) = (term673 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5426254 A i j f s)). Qed.
Lemma lem5426256 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426257 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term661 A i f s) = (term674 A i f s).
Proof. exact (MK_COMB (@lem5426256) (@lem5426255 A i f s)). Qed.
Lemma lem5426258 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : ((term660 A i f s) = (term661 A i f s)) = ((term656 A i f s) = (term674 A i f s)).
Proof. exact (MK_COMB (@lem5426249 A i f s) (@lem5426257 A i f s)). Qed.
Lemma lem5426259 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term656 A i f s) = (term674 A i f s).
Proof. exact (EQ_MP (@lem5426258 A i f s) (@lem5426239 A i f s)). Qed.
Lemma lem5426260 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term658 A f s) = (term675 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5426259 A i f s)). Qed.
Lemma lem5426261 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426262 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term659 A f s) = (term676 A f s).
Proof. exact (MK_COMB (@lem5426261) (@lem5426260 A f s)). Qed.
Lemma lem5426263 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term596 A f s) = (term676 A f s).
Proof. exact (TRANS (@lem5426235 A f s) (@lem5426262 A f s)). Qed.
Lemma lem5426264 {A : Type'} (s : A -> Prop) : (term605 A s) = (term677 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426263 A f s)). Qed.
Lemma lem5426265 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5426266 {A : Type'} (s : A -> Prop) : (term606 A s) = (term678 A s).
Proof. exact (MK_COMB (@lem5426265 A) (@lem5426264 A s)). Qed.
Lemma lem5426268 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5426269 {A : Type'} (P : type973 A) : (term299 A P) = (term300 A P).
Proof. exact (@lem5426268 (nat -> A) nat P). Qed.
Lemma lem5426270 {A : Type'} (s : A -> Prop) : (term679 A s) = (term680 A s).
Proof. exact (@lem5426269 A (term681 A s)). Qed.
Lemma lem5426271 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term682 A s f) = (term675 A f s).
Proof. exact (eq_refl (term682 A s f)). Qed.
Lemma lem5426272 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5426273 {A : Type'} (f : nat -> A) (s : A -> Prop) (i : nat) : (term683 A s f i) = (term684 A f s i).
Proof. exact (MK_COMB (@lem5426271 A f s) (@lem5426272 i)). Qed.
Lemma lem5426274 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term684 A f s i) = (term674 A i f s).
Proof. exact (eq_refl (term684 A f s i)). Qed.
Lemma lem5426275 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term683 A s f i) = (term674 A i f s).
Proof. exact (TRANS (@lem5426273 A f s i) (@lem5426274 A i f s)). Qed.
Lemma lem5426276 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term685 A s f) = (term675 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5426275 A i f s)). Qed.
Lemma lem5426277 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426278 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term686 A s f) = (term676 A f s).
Proof. exact (MK_COMB (@lem5426277) (@lem5426276 A f s)). Qed.
Lemma lem5426279 {A : Type'} (s : A -> Prop) : (term687 A s) = (term677 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426278 A f s)). Qed.
Lemma lem5426280 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5426281 {A : Type'} (s : A -> Prop) : (term679 A s) = (term678 A s).
Proof. exact (MK_COMB (@lem5426280 A) (@lem5426279 A s)). Qed.
Lemma lem5426282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426283 {A : Type'} (s : A -> Prop) : (term688 A s) = (term689 A s).
Proof. exact (MK_COMB (@lem5426282) (@lem5426281 A s)). Qed.
Lemma lem5426284 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term682 A s f) = (term675 A f s).
Proof. exact (eq_refl (term682 A s f)). Qed.
Lemma lem5426285 {A : Type'} (i : type977 A) (f : nat -> A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem5426286 {A : Type'} (s : A -> Prop) (i : type977 A) (f : nat -> A) : (term690 A s i f) = (term691 A s i f).
Proof. exact (MK_COMB (@lem5426284 A f s) (@lem5426285 A i f)). Qed.
Lemma lem5426287 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term691 A s i f) = (term692 A i f s).
Proof. exact (eq_refl (term691 A s i f)). Qed.
Lemma lem5426288 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term690 A s i f) = (term692 A i f s).
Proof. exact (TRANS (@lem5426286 A s i f) (@lem5426287 A i f s)). Qed.
Lemma lem5426289 {A : Type'} (i : type977 A) (s : A -> Prop) : (term693 A s i) = (term694 A i s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426288 A i f s)). Qed.
Lemma lem5426290 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5426291 {A : Type'} (i : type977 A) (s : A -> Prop) : (term695 A s i) = (term696 A i s).
Proof. exact (MK_COMB (@lem5426290 A) (@lem5426289 A i s)). Qed.
Lemma lem5426292 {A : Type'} (s : A -> Prop) : (term697 A s) = (term698 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426291 A i s)). Qed.
Lemma lem5426293 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426294 {A : Type'} (s : A -> Prop) : (term680 A s) = (term699 A s).
Proof. exact (MK_COMB (@lem5426293 A) (@lem5426292 A s)). Qed.
Lemma lem5426295 {A : Type'} (s : A -> Prop) : ((term679 A s) = (term680 A s)) = ((term678 A s) = (term699 A s)).
Proof. exact (MK_COMB (@lem5426283 A s) (@lem5426294 A s)). Qed.
Lemma lem5426296 {A : Type'} (s : A -> Prop) : (term678 A s) = (term699 A s).
Proof. exact (EQ_MP (@lem5426295 A s) (@lem5426270 A s)). Qed.
Lemma lem5426298 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5426299 {A : Type'} (P : type973 A) : (term299 A P) = (term300 A P).
Proof. exact (@lem5426298 (nat -> A) nat P). Qed.
Lemma lem5426300 {A : Type'} (i : type977 A) (s : A -> Prop) : (term700 A i s) = (term701 A i s).
Proof. exact (@lem5426299 A (term702 A i s)). Qed.
Lemma lem5426301 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term703 A i s f) = (term704 A i f s).
Proof. exact (eq_refl (term703 A i s f)). Qed.
Lemma lem5426302 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5426303 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) (j : nat) : (term705 A i s f j) = (term706 A i f s j).
Proof. exact (MK_COMB (@lem5426301 A i f s) (@lem5426302 j)). Qed.
Lemma lem5426304 {A : Type'} (i : type977 A) (j : nat) (f : nat -> A) (s : A -> Prop) : (term706 A i f s j) = (term707 A i j f s).
Proof. exact (eq_refl (term706 A i f s j)). Qed.
Lemma lem5426305 {A : Type'} (i : type977 A) (j : nat) (f : nat -> A) (s : A -> Prop) : (term705 A i s f j) = (term707 A i j f s).
Proof. exact (TRANS (@lem5426303 A i f s j) (@lem5426304 A i j f s)). Qed.
Lemma lem5426306 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term708 A i s f) = (term704 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5426305 A i j f s)). Qed.
Lemma lem5426307 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426308 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term709 A i s f) = (term692 A i f s).
Proof. exact (MK_COMB (@lem5426307) (@lem5426306 A i f s)). Qed.
Lemma lem5426309 {A : Type'} (i : type977 A) (s : A -> Prop) : (term710 A i s) = (term694 A i s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426308 A i f s)). Qed.
Lemma lem5426310 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5426311 {A : Type'} (i : type977 A) (s : A -> Prop) : (term700 A i s) = (term696 A i s).
Proof. exact (MK_COMB (@lem5426310 A) (@lem5426309 A i s)). Qed.
Lemma lem5426312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426313 {A : Type'} (i : type977 A) (s : A -> Prop) : (term711 A i s) = (term712 A i s).
Proof. exact (MK_COMB (@lem5426312) (@lem5426311 A i s)). Qed.
Lemma lem5426314 {A : Type'} (i : type977 A) (f : nat -> A) (s : A -> Prop) : (term703 A i s f) = (term704 A i f s).
Proof. exact (eq_refl (term703 A i s f)). Qed.
Lemma lem5426315 {A : Type'} (j : type977 A) (f : nat -> A) : (j f) = (j f).
Proof. exact (eq_refl (j f)). Qed.
Lemma lem5426316 {A : Type'} (i : type977 A) (s : A -> Prop) (j : type977 A) (f : nat -> A) : (term713 A i s j f) = (term714 A i s j f).
Proof. exact (MK_COMB (@lem5426314 A i f s) (@lem5426315 A j f)). Qed.
Lemma lem5426317 {A : Type'} (i : type977 A) (j : type977 A) (f : nat -> A) (s : A -> Prop) : (term714 A i s j f) = (term715 A i j f s).
Proof. exact (eq_refl (term714 A i s j f)). Qed.
Lemma lem5426318 {A : Type'} (i : type977 A) (j : type977 A) (f : nat -> A) (s : A -> Prop) : (term713 A i s j f) = (term715 A i j f s).
Proof. exact (TRANS (@lem5426316 A i s j f) (@lem5426317 A i j f s)). Qed.
Lemma lem5426319 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) : (term716 A i s j) = (term717 A i j s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426318 A i j f s)). Qed.
Lemma lem5426320 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5426321 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) : (term718 A i s j) = (term719 A i j s).
Proof. exact (MK_COMB (@lem5426320 A) (@lem5426319 A i j s)). Qed.
Lemma lem5426322 {A : Type'} (i : type977 A) (s : A -> Prop) : (term720 A i s) = (term721 A i s).
Proof. exact (fun_ext (fun j : type977 A => @lem5426321 A i j s)). Qed.
Lemma lem5426323 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426324 {A : Type'} (i : type977 A) (s : A -> Prop) : (term701 A i s) = (term722 A i s).
Proof. exact (MK_COMB (@lem5426323 A) (@lem5426322 A i s)). Qed.
Lemma lem5426325 {A : Type'} (i : type977 A) (s : A -> Prop) : ((term700 A i s) = (term701 A i s)) = ((term696 A i s) = (term722 A i s)).
Proof. exact (MK_COMB (@lem5426313 A i s) (@lem5426324 A i s)). Qed.
Lemma lem5426326 {A : Type'} (i : type977 A) (s : A -> Prop) : (term696 A i s) = (term722 A i s).
Proof. exact (EQ_MP (@lem5426325 A i s) (@lem5426300 A i s)). Qed.
Lemma lem5426327 {A : Type'} (s : A -> Prop) : (term698 A s) = (term723 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426326 A i s)). Qed.
Lemma lem5426328 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426329 {A : Type'} (s : A -> Prop) : (term699 A s) = (term724 A s).
Proof. exact (MK_COMB (@lem5426328 A) (@lem5426327 A s)). Qed.
Lemma lem5426330 {A : Type'} (s : A -> Prop) : (term678 A s) = (term724 A s).
Proof. exact (TRANS (@lem5426296 A s) (@lem5426329 A s)). Qed.
Lemma lem5426331 {A : Type'} (s : A -> Prop) : (term606 A s) = (term724 A s).
Proof. exact (TRANS (@lem5426266 A s) (@lem5426330 A s)). Qed.
Lemma lem5426332 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5426333 {A : Type'} (s : A -> Prop) : (term614 A s) = (term725 A s).
Proof. exact (MK_COMB (@lem5426332 A s) (@lem5426331 A s)). Qed.
Lemma lem5426335 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5426336 {A : Type'} (P : Prop) (Q : type246 A) : (term726 A P Q) = (term727 A P Q).
Proof. exact (@lem5426335 (type977 A) P Q). Qed.
Lemma lem5426337 {A : Type'} (s : A -> Prop) : (term728 A s) = (term729 A s).
Proof. exact (@lem5426336 A (@FINITE A s) (term723 A s)). Qed.
Lemma lem5426338 {A : Type'} (i : type977 A) (s : A -> Prop) : (term730 A s i) = (term722 A i s).
Proof. exact (eq_refl (term730 A s i)). Qed.
Lemma lem5426339 {A : Type'} (s : A -> Prop) : (term731 A s) = (term723 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426338 A i s)). Qed.
Lemma lem5426340 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426341 {A : Type'} (s : A -> Prop) : (term732 A s) = (term724 A s).
Proof. exact (MK_COMB (@lem5426340 A) (@lem5426339 A s)). Qed.
Lemma lem5426342 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5426343 {A : Type'} (s : A -> Prop) : (term728 A s) = (term725 A s).
Proof. exact (MK_COMB (@lem5426342 A s) (@lem5426341 A s)). Qed.
Lemma lem5426344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426345 {A : Type'} (s : A -> Prop) : (term733 A s) = (term734 A s).
Proof. exact (MK_COMB (@lem5426344) (@lem5426343 A s)). Qed.
Lemma lem5426346 {A : Type'} (i : type977 A) (s : A -> Prop) : (term730 A s i) = (term722 A i s).
Proof. exact (eq_refl (term730 A s i)). Qed.
Lemma lem5426347 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5426348 {A : Type'} (i : type977 A) (s : A -> Prop) : (term735 A s i) = (term736 A i s).
Proof. exact (MK_COMB (@lem5426347 A s) (@lem5426346 A i s)). Qed.
Lemma lem5426349 {A : Type'} (s : A -> Prop) : (term737 A s) = (term738 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426348 A i s)). Qed.
Lemma lem5426350 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426351 {A : Type'} (s : A -> Prop) : (term729 A s) = (term739 A s).
Proof. exact (MK_COMB (@lem5426350 A) (@lem5426349 A s)). Qed.
Lemma lem5426352 {A : Type'} (s : A -> Prop) : ((term728 A s) = (term729 A s)) = ((term725 A s) = (term739 A s)).
Proof. exact (MK_COMB (@lem5426345 A s) (@lem5426351 A s)). Qed.
Lemma lem5426353 {A : Type'} (s : A -> Prop) : (term725 A s) = (term739 A s).
Proof. exact (EQ_MP (@lem5426352 A s) (@lem5426337 A s)). Qed.
Lemma lem5426355 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5426356 {A : Type'} (P : Prop) (Q : type246 A) : (term726 A P Q) = (term727 A P Q).
Proof. exact (@lem5426355 (type977 A) P Q). Qed.
Lemma lem5426357 {A : Type'} (i : type977 A) (s : A -> Prop) : (term740 A i s) = (term741 A i s).
Proof. exact (@lem5426356 A (@FINITE A s) (term721 A i s)). Qed.
Lemma lem5426358 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) : (term742 A i s j) = (term719 A i j s).
Proof. exact (eq_refl (term742 A i s j)). Qed.
Lemma lem5426359 {A : Type'} (i : type977 A) (s : A -> Prop) : (term743 A i s) = (term721 A i s).
Proof. exact (fun_ext (fun j : type977 A => @lem5426358 A i j s)). Qed.
Lemma lem5426360 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426361 {A : Type'} (i : type977 A) (s : A -> Prop) : (term744 A i s) = (term722 A i s).
Proof. exact (MK_COMB (@lem5426360 A) (@lem5426359 A i s)). Qed.
Lemma lem5426362 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5426363 {A : Type'} (i : type977 A) (s : A -> Prop) : (term740 A i s) = (term736 A i s).
Proof. exact (MK_COMB (@lem5426362 A s) (@lem5426361 A i s)). Qed.
Lemma lem5426364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426365 {A : Type'} (i : type977 A) (s : A -> Prop) : (term745 A i s) = (term746 A i s).
Proof. exact (MK_COMB (@lem5426364) (@lem5426363 A i s)). Qed.
Lemma lem5426366 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) : (term742 A i s j) = (term719 A i j s).
Proof. exact (eq_refl (term742 A i s j)). Qed.
Lemma lem5426367 {A : Type'} (s : A -> Prop) : (term612 A s) = (term612 A s).
Proof. exact (eq_refl (term612 A s)). Qed.
Lemma lem5426368 {A : Type'} (i : type977 A) (j : type977 A) (s : A -> Prop) : (term747 A i s j) = (term748 A i j s).
Proof. exact (MK_COMB (@lem5426367 A s) (@lem5426366 A i j s)). Qed.
Lemma lem5426369 {A : Type'} (i : type977 A) (s : A -> Prop) : (term749 A i s) = (term750 A i s).
Proof. exact (fun_ext (fun j : type977 A => @lem5426368 A i j s)). Qed.
Lemma lem5426370 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426371 {A : Type'} (i : type977 A) (s : A -> Prop) : (term741 A i s) = (term751 A i s).
Proof. exact (MK_COMB (@lem5426370 A) (@lem5426369 A i s)). Qed.
Lemma lem5426372 {A : Type'} (i : type977 A) (s : A -> Prop) : ((term740 A i s) = (term741 A i s)) = ((term736 A i s) = (term751 A i s)).
Proof. exact (MK_COMB (@lem5426365 A i s) (@lem5426371 A i s)). Qed.
Lemma lem5426373 {A : Type'} (i : type977 A) (s : A -> Prop) : (term736 A i s) = (term751 A i s).
Proof. exact (EQ_MP (@lem5426372 A i s) (@lem5426357 A i s)). Qed.
Lemma lem5426374 {A : Type'} (s : A -> Prop) : (term738 A s) = (term752 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426373 A i s)). Qed.
Lemma lem5426375 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426376 {A : Type'} (s : A -> Prop) : (term739 A s) = (term753 A s).
Proof. exact (MK_COMB (@lem5426375 A) (@lem5426374 A s)). Qed.
Lemma lem5426377 {A : Type'} (s : A -> Prop) : (term725 A s) = (term753 A s).
Proof. exact (TRANS (@lem5426353 A s) (@lem5426376 A s)). Qed.
Lemma lem5426378 {A : Type'} (s : A -> Prop) : (term614 A s) = (term753 A s).
Proof. exact (TRANS (@lem5426333 A s) (@lem5426377 A s)). Qed.
Lemma lem5426379 {A : Type'} : (term627 A) = (term754 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426378 A s)). Qed.
Lemma lem5426380 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426381 {A : Type'} : (term638 A) = (term755 A).
Proof. exact (MK_COMB (@lem5426380 A) (@lem5426379 A)). Qed.
Lemma lem5426383 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5426384 {A : Type'} (P : type608 A) : (term756 A P) = (term757 A P).
Proof. exact (@lem5426383 (A -> Prop) (type977 A) P). Qed.
Lemma lem5426385 {A : Type'} : (term758 A) = (term759 A).
Proof. exact (@lem5426384 A (term760 A)). Qed.
Lemma lem5426386 {A : Type'} (s : A -> Prop) : (term761 A s) = (term752 A s).
Proof. exact (eq_refl (term761 A s)). Qed.
Lemma lem5426387 {A : Type'} (i : type977 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5426388 {A : Type'} (s : A -> Prop) (i : type977 A) : (term762 A s i) = (term763 A s i).
Proof. exact (MK_COMB (@lem5426386 A s) (@lem5426387 A i)). Qed.
Lemma lem5426389 {A : Type'} (i : type977 A) (s : A -> Prop) : (term763 A s i) = (term751 A i s).
Proof. exact (eq_refl (term763 A s i)). Qed.
Lemma lem5426390 {A : Type'} (i : type977 A) (s : A -> Prop) : (term762 A s i) = (term751 A i s).
Proof. exact (TRANS (@lem5426388 A s i) (@lem5426389 A i s)). Qed.
Lemma lem5426391 {A : Type'} (s : A -> Prop) : (term764 A s) = (term752 A s).
Proof. exact (fun_ext (fun i : type977 A => @lem5426390 A i s)). Qed.
Lemma lem5426392 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426393 {A : Type'} (s : A -> Prop) : (term765 A s) = (term753 A s).
Proof. exact (MK_COMB (@lem5426392 A) (@lem5426391 A s)). Qed.
Lemma lem5426394 {A : Type'} : (term766 A) = (term754 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426393 A s)). Qed.
Lemma lem5426395 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426396 {A : Type'} : (term758 A) = (term755 A).
Proof. exact (MK_COMB (@lem5426395 A) (@lem5426394 A)). Qed.
Lemma lem5426397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426398 {A : Type'} : (term767 A) = (term768 A).
Proof. exact (MK_COMB (@lem5426397) (@lem5426396 A)). Qed.
Lemma lem5426399 {A : Type'} (s : A -> Prop) : (term761 A s) = (term752 A s).
Proof. exact (eq_refl (term761 A s)). Qed.
Lemma lem5426400 {A : Type'} (i : type661 A) (s : A -> Prop) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem5426401 {A : Type'} (i : type661 A) (s : A -> Prop) : (term769 A i s) = (term770 A i s).
Proof. exact (MK_COMB (@lem5426399 A s) (@lem5426400 A i s)). Qed.
Lemma lem5426402 {A : Type'} (i : type661 A) (s : A -> Prop) : (term770 A i s) = (term771 A i s).
Proof. exact (eq_refl (term770 A i s)). Qed.
Lemma lem5426403 {A : Type'} (i : type661 A) (s : A -> Prop) : (term769 A i s) = (term771 A i s).
Proof. exact (TRANS (@lem5426401 A i s) (@lem5426402 A i s)). Qed.
Lemma lem5426404 {A : Type'} (i : type661 A) : (term772 A i) = (term773 A i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426403 A i s)). Qed.
Lemma lem5426405 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426406 {A : Type'} (i : type661 A) : (term774 A i) = (term775 A i).
Proof. exact (MK_COMB (@lem5426405 A) (@lem5426404 A i)). Qed.
Lemma lem5426407 {A : Type'} : (term776 A) = (term777 A).
Proof. exact (fun_ext (fun i : type661 A => @lem5426406 A i)). Qed.
Lemma lem5426408 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426409 {A : Type'} : (term759 A) = (term778 A).
Proof. exact (MK_COMB (@lem5426408 A) (@lem5426407 A)). Qed.
Lemma lem5426410 {A : Type'} : ((term758 A) = (term759 A)) = ((term755 A) = (term778 A)).
Proof. exact (MK_COMB (@lem5426398 A) (@lem5426409 A)). Qed.
Lemma lem5426411 {A : Type'} : (term755 A) = (term778 A).
Proof. exact (EQ_MP (@lem5426410 A) (@lem5426385 A)). Qed.
Lemma lem5426413 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5426414 {A : Type'} (P : type608 A) : (term756 A P) = (term757 A P).
Proof. exact (@lem5426413 (A -> Prop) (type977 A) P). Qed.
Lemma lem5426415 {A : Type'} (i : type661 A) : (term779 A i) = (term780 A i).
Proof. exact (@lem5426414 A (term781 A i)). Qed.
Lemma lem5426416 {A : Type'} (i : type661 A) (s : A -> Prop) : (term782 A i s) = (term783 A i s).
Proof. exact (eq_refl (term782 A i s)). Qed.
Lemma lem5426417 {A : Type'} (j : type977 A) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5426418 {A : Type'} (i : type661 A) (s : A -> Prop) (j : type977 A) : (term784 A i s j) = (term785 A i s j).
Proof. exact (MK_COMB (@lem5426416 A i s) (@lem5426417 A j)). Qed.
Lemma lem5426419 {A : Type'} (i : type661 A) (j : type977 A) (s : A -> Prop) : (term785 A i s j) = (term786 A i j s).
Proof. exact (eq_refl (term785 A i s j)). Qed.
Lemma lem5426420 {A : Type'} (i : type661 A) (j : type977 A) (s : A -> Prop) : (term784 A i s j) = (term786 A i j s).
Proof. exact (TRANS (@lem5426418 A i s j) (@lem5426419 A i j s)). Qed.
Lemma lem5426421 {A : Type'} (i : type661 A) (s : A -> Prop) : (term787 A i s) = (term783 A i s).
Proof. exact (fun_ext (fun j : type977 A => @lem5426420 A i j s)). Qed.
Lemma lem5426422 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem5426423 {A : Type'} (i : type661 A) (s : A -> Prop) : (term788 A i s) = (term771 A i s).
Proof. exact (MK_COMB (@lem5426422 A) (@lem5426421 A i s)). Qed.
Lemma lem5426424 {A : Type'} (i : type661 A) : (term789 A i) = (term773 A i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426423 A i s)). Qed.
Lemma lem5426425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426426 {A : Type'} (i : type661 A) : (term779 A i) = (term775 A i).
Proof. exact (MK_COMB (@lem5426425 A) (@lem5426424 A i)). Qed.
Lemma lem5426427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426428 {A : Type'} (i : type661 A) : (term790 A i) = (term791 A i).
Proof. exact (MK_COMB (@lem5426427) (@lem5426426 A i)). Qed.
Lemma lem5426429 {A : Type'} (i : type661 A) (s : A -> Prop) : (term782 A i s) = (term783 A i s).
Proof. exact (eq_refl (term782 A i s)). Qed.
Lemma lem5426430 {A : Type'} (j : type661 A) (s : A -> Prop) : (j s) = (j s).
Proof. exact (eq_refl (j s)). Qed.
Lemma lem5426431 {A : Type'} (i : type661 A) (j : type661 A) (s : A -> Prop) : (term792 A i j s) = (term793 A i j s).
Proof. exact (MK_COMB (@lem5426429 A i s) (@lem5426430 A j s)). Qed.
Lemma lem5426432 {A : Type'} (i : type661 A) (j : type661 A) (s : A -> Prop) : (term793 A i j s) = (term794 A i j s).
Proof. exact (eq_refl (term793 A i j s)). Qed.
Lemma lem5426433 {A : Type'} (i : type661 A) (j : type661 A) (s : A -> Prop) : (term792 A i j s) = (term794 A i j s).
Proof. exact (TRANS (@lem5426431 A i j s) (@lem5426432 A i j s)). Qed.
Lemma lem5426434 {A : Type'} (i : type661 A) (j : type661 A) : (term795 A i j) = (term796 A i j).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426433 A i j s)). Qed.
Lemma lem5426435 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426436 {A : Type'} (i : type661 A) (j : type661 A) : (term797 A i j) = (term798 A i j).
Proof. exact (MK_COMB (@lem5426435 A) (@lem5426434 A i j)). Qed.
Lemma lem5426437 {A : Type'} (i : type661 A) : (term799 A i) = (term800 A i).
Proof. exact (fun_ext (fun j : type661 A => @lem5426436 A i j)). Qed.
Lemma lem5426438 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426439 {A : Type'} (i : type661 A) : (term780 A i) = (term801 A i).
Proof. exact (MK_COMB (@lem5426438 A) (@lem5426437 A i)). Qed.
Lemma lem5426440 {A : Type'} (i : type661 A) : ((term779 A i) = (term780 A i)) = ((term775 A i) = (term801 A i)).
Proof. exact (MK_COMB (@lem5426428 A i) (@lem5426439 A i)). Qed.
Lemma lem5426441 {A : Type'} (i : type661 A) : (term775 A i) = (term801 A i).
Proof. exact (EQ_MP (@lem5426440 A i) (@lem5426415 A i)). Qed.
Lemma lem5426442 {A : Type'} : (term777 A) = (term802 A).
Proof. exact (fun_ext (fun i : type661 A => @lem5426441 A i)). Qed.
Lemma lem5426443 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426444 {A : Type'} : (term778 A) = (term803 A).
Proof. exact (MK_COMB (@lem5426443 A) (@lem5426442 A)). Qed.
Lemma lem5426445 {A : Type'} : (term755 A) = (term803 A).
Proof. exact (TRANS (@lem5426411 A) (@lem5426444 A)). Qed.
Lemma lem5426446 {A : Type'} : (term638 A) = (term803 A).
Proof. exact (TRANS (@lem5426381 A) (@lem5426445 A)). Qed.
Lemma lem5426447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426448 {A : Type'} : (term640 A) = (term804 A).
Proof. exact (MK_COMB (@lem5426447) (@lem5426446 A)). Qed.
Lemma lem5426450 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5426451 {A : Type'} (P : Prop) (Q : type976 A) : (term531 A P Q) = (term532 A P Q).
Proof. exact (@lem5426450 (nat -> A) P Q). Qed.
Lemma lem5426452 {A : Type'} (s : A -> Prop) : (term805 A s) = (term806 A s).
Proof. exact (@lem5426451 A (term435 A s) (term607 A s)). Qed.
Lemma lem5426453 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term807 A s f) = (term599 A f s).
Proof. exact (eq_refl (term807 A s f)). Qed.
Lemma lem5426454 {A : Type'} (s : A -> Prop) : (term808 A s) = (term607 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426453 A f s)). Qed.
Lemma lem5426455 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5426456 {A : Type'} (s : A -> Prop) : (term809 A s) = (term608 A s).
Proof. exact (MK_COMB (@lem5426455 A) (@lem5426454 A s)). Qed.
Lemma lem5426457 {A : Type'} (s : A -> Prop) : (term609 A s) = (term609 A s).
Proof. exact (eq_refl (term609 A s)). Qed.
Lemma lem5426458 {A : Type'} (s : A -> Prop) : (term805 A s) = (term611 A s).
Proof. exact (MK_COMB (@lem5426457 A s) (@lem5426456 A s)). Qed.
Lemma lem5426459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426460 {A : Type'} (s : A -> Prop) : (term810 A s) = (term811 A s).
Proof. exact (MK_COMB (@lem5426459) (@lem5426458 A s)). Qed.
Lemma lem5426461 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term807 A s f) = (term599 A f s).
Proof. exact (eq_refl (term807 A s f)). Qed.
Lemma lem5426462 {A : Type'} (s : A -> Prop) : (term609 A s) = (term609 A s).
Proof. exact (eq_refl (term609 A s)). Qed.
Lemma lem5426463 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term812 A s f) = (term813 A f s).
Proof. exact (MK_COMB (@lem5426462 A s) (@lem5426461 A f s)). Qed.
Lemma lem5426464 {A : Type'} (s : A -> Prop) : (term814 A s) = (term815 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426463 A f s)). Qed.
Lemma lem5426465 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5426466 {A : Type'} (s : A -> Prop) : (term806 A s) = (term816 A s).
Proof. exact (MK_COMB (@lem5426465 A) (@lem5426464 A s)). Qed.
Lemma lem5426467 {A : Type'} (s : A -> Prop) : ((term805 A s) = (term806 A s)) = ((term611 A s) = (term816 A s)).
Proof. exact (MK_COMB (@lem5426460 A s) (@lem5426466 A s)). Qed.
Lemma lem5426468 {A : Type'} (s : A -> Prop) : (term611 A s) = (term816 A s).
Proof. exact (EQ_MP (@lem5426467 A s) (@lem5426452 A s)). Qed.
Lemma lem5426469 {A : Type'} : (term628 A) = (term817 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426468 A s)). Qed.
Lemma lem5426470 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426471 {A : Type'} : (term643 A) = (term818 A).
Proof. exact (MK_COMB (@lem5426470 A) (@lem5426469 A)). Qed.
Lemma lem5426473 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5426474 {A : Type'} (P : type660 A) : (term819 A P) = (term820 A P).
Proof. exact (@lem5426473 (A -> Prop) (nat -> A) P). Qed.
Lemma lem5426475 {A : Type'} : (term821 A) = (term822 A).
Proof. exact (@lem5426474 A (term823 A)). Qed.
Lemma lem5426476 {A : Type'} (s : A -> Prop) : (term824 A s) = (term815 A s).
Proof. exact (eq_refl (term824 A s)). Qed.
Lemma lem5426477 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5426478 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term825 A s f) = (term826 A s f).
Proof. exact (MK_COMB (@lem5426476 A s) (@lem5426477 A f)). Qed.
Lemma lem5426479 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term826 A s f) = (term813 A f s).
Proof. exact (eq_refl (term826 A s f)). Qed.
Lemma lem5426480 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term825 A s f) = (term813 A f s).
Proof. exact (TRANS (@lem5426478 A s f) (@lem5426479 A f s)). Qed.
Lemma lem5426481 {A : Type'} (s : A -> Prop) : (term827 A s) = (term815 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5426480 A f s)). Qed.
Lemma lem5426482 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5426483 {A : Type'} (s : A -> Prop) : (term828 A s) = (term816 A s).
Proof. exact (MK_COMB (@lem5426482 A) (@lem5426481 A s)). Qed.
Lemma lem5426484 {A : Type'} : (term829 A) = (term817 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426483 A s)). Qed.
Lemma lem5426485 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426486 {A : Type'} : (term821 A) = (term818 A).
Proof. exact (MK_COMB (@lem5426485 A) (@lem5426484 A)). Qed.
Lemma lem5426487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426488 {A : Type'} : (term830 A) = (term831 A).
Proof. exact (MK_COMB (@lem5426487) (@lem5426486 A)). Qed.
Lemma lem5426489 {A : Type'} (s : A -> Prop) : (term824 A s) = (term815 A s).
Proof. exact (eq_refl (term824 A s)). Qed.
Lemma lem5426490 {A : Type'} (f : type681 A) (s : A -> Prop) : (f s) = (f s).
Proof. exact (eq_refl (f s)). Qed.
Lemma lem5426491 {A : Type'} (f : type681 A) (s : A -> Prop) : (term832 A f s) = (term833 A f s).
Proof. exact (MK_COMB (@lem5426489 A s) (@lem5426490 A f s)). Qed.
Lemma lem5426492 {A : Type'} (f : type681 A) (s : A -> Prop) : (term833 A f s) = (term834 A f s).
Proof. exact (eq_refl (term833 A f s)). Qed.
Lemma lem5426493 {A : Type'} (f : type681 A) (s : A -> Prop) : (term832 A f s) = (term834 A f s).
Proof. exact (TRANS (@lem5426491 A f s) (@lem5426492 A f s)). Qed.
Lemma lem5426494 {A : Type'} (f : type681 A) : (term835 A f) = (term836 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5426493 A f s)). Qed.
Lemma lem5426495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5426496 {A : Type'} (f : type681 A) : (term837 A f) = (term838 A f).
Proof. exact (MK_COMB (@lem5426495 A) (@lem5426494 A f)). Qed.
Lemma lem5426497 {A : Type'} : (term839 A) = (term840 A).
Proof. exact (fun_ext (fun f : type681 A => @lem5426496 A f)). Qed.
Lemma lem5426498 {A : Type'} : (@ex ((A -> Prop) -> nat -> A)) = (@ex ((A -> Prop) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> nat -> A))). Qed.
Lemma lem5426499 {A : Type'} : (term822 A) = (term841 A).
Proof. exact (MK_COMB (@lem5426498 A) (@lem5426497 A)). Qed.
Lemma lem5426500 {A : Type'} : ((term821 A) = (term822 A)) = ((term818 A) = (term841 A)).
Proof. exact (MK_COMB (@lem5426488 A) (@lem5426499 A)). Qed.
Lemma lem5426501 {A : Type'} : (term818 A) = (term841 A).
Proof. exact (EQ_MP (@lem5426500 A) (@lem5426475 A)). Qed.
Lemma lem5426502 {A : Type'} : (term643 A) = (term841 A).
Proof. exact (TRANS (@lem5426471 A) (@lem5426501 A)). Qed.
Lemma lem5426503 {A : Type'} : (term644 A) = (term842 A).
Proof. exact (MK_COMB (@lem5426448 A) (@lem5426502 A)). Qed.
Lemma lem5426505 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5426506 {A : Type'} (P : type148 A) (Q : Prop) : (term845 A P Q) = (term846 A P Q).
Proof. exact (@lem5426505 (type661 A) P Q). Qed.
Lemma lem5426507 {A : Type'} : (term847 A) = (term848 A).
Proof. exact (@lem5426506 A (term802 A) (term841 A)). Qed.
Lemma lem5426508 {A : Type'} (i : type661 A) : (term849 A i) = (term801 A i).
Proof. exact (eq_refl (term849 A i)). Qed.
Lemma lem5426509 {A : Type'} : (term850 A) = (term802 A).
Proof. exact (fun_ext (fun i : type661 A => @lem5426508 A i)). Qed.
Lemma lem5426510 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426511 {A : Type'} : (term851 A) = (term803 A).
Proof. exact (MK_COMB (@lem5426510 A) (@lem5426509 A)). Qed.
Lemma lem5426512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426513 {A : Type'} : (term852 A) = (term804 A).
Proof. exact (MK_COMB (@lem5426512) (@lem5426511 A)). Qed.
Lemma lem5426514 {A : Type'} : (term841 A) = (term841 A).
Proof. exact (eq_refl (term841 A)). Qed.
Lemma lem5426515 {A : Type'} : (term847 A) = (term842 A).
Proof. exact (MK_COMB (@lem5426513 A) (@lem5426514 A)). Qed.
Lemma lem5426516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426517 {A : Type'} : (term853 A) = (term854 A).
Proof. exact (MK_COMB (@lem5426516) (@lem5426515 A)). Qed.
Lemma lem5426518 {A : Type'} (i : type661 A) : (term849 A i) = (term801 A i).
Proof. exact (eq_refl (term849 A i)). Qed.
Lemma lem5426519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426520 {A : Type'} (i : type661 A) : (term855 A i) = (term856 A i).
Proof. exact (MK_COMB (@lem5426519) (@lem5426518 A i)). Qed.
Lemma lem5426521 {A : Type'} : (term841 A) = (term841 A).
Proof. exact (eq_refl (term841 A)). Qed.
Lemma lem5426522 {A : Type'} (i : type661 A) : (term857 A i) = (term858 A i).
Proof. exact (MK_COMB (@lem5426520 A i) (@lem5426521 A)). Qed.
Lemma lem5426523 {A : Type'} : (term859 A) = (term860 A).
Proof. exact (fun_ext (fun i : type661 A => @lem5426522 A i)). Qed.
Lemma lem5426524 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426525 {A : Type'} : (term848 A) = (term861 A).
Proof. exact (MK_COMB (@lem5426524 A) (@lem5426523 A)). Qed.
Lemma lem5426526 {A : Type'} : ((term847 A) = (term848 A)) = ((term842 A) = (term861 A)).
Proof. exact (MK_COMB (@lem5426517 A) (@lem5426525 A)). Qed.
Lemma lem5426527 {A : Type'} : (term842 A) = (term861 A).
Proof. exact (EQ_MP (@lem5426526 A) (@lem5426507 A)). Qed.
Lemma lem5426529 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5426530 {A : Type'} (P : type148 A) (Q : Prop) : (term845 A P Q) = (term846 A P Q).
Proof. exact (@lem5426529 (type661 A) P Q). Qed.
Lemma lem5426531 {A : Type'} (i : type661 A) : (term862 A i) = (term863 A i).
Proof. exact (@lem5426530 A (term800 A i) (term841 A)). Qed.
Lemma lem5426532 {A : Type'} (i : type661 A) (j : type661 A) : (term864 A i j) = (term798 A i j).
Proof. exact (eq_refl (term864 A i j)). Qed.
Lemma lem5426533 {A : Type'} (i : type661 A) : (term865 A i) = (term800 A i).
Proof. exact (fun_ext (fun j : type661 A => @lem5426532 A i j)). Qed.
Lemma lem5426534 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426535 {A : Type'} (i : type661 A) : (term866 A i) = (term801 A i).
Proof. exact (MK_COMB (@lem5426534 A) (@lem5426533 A i)). Qed.
Lemma lem5426536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426537 {A : Type'} (i : type661 A) : (term867 A i) = (term856 A i).
Proof. exact (MK_COMB (@lem5426536) (@lem5426535 A i)). Qed.
Lemma lem5426538 {A : Type'} : (term841 A) = (term841 A).
Proof. exact (eq_refl (term841 A)). Qed.
Lemma lem5426539 {A : Type'} (i : type661 A) : (term862 A i) = (term858 A i).
Proof. exact (MK_COMB (@lem5426537 A i) (@lem5426538 A)). Qed.
Lemma lem5426540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426541 {A : Type'} (i : type661 A) : (term868 A i) = (term869 A i).
Proof. exact (MK_COMB (@lem5426540) (@lem5426539 A i)). Qed.
Lemma lem5426542 {A : Type'} (i : type661 A) (j : type661 A) : (term864 A i j) = (term798 A i j).
Proof. exact (eq_refl (term864 A i j)). Qed.
Lemma lem5426543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426544 {A : Type'} (i : type661 A) (j : type661 A) : (term870 A i j) = (term871 A i j).
Proof. exact (MK_COMB (@lem5426543) (@lem5426542 A i j)). Qed.
Lemma lem5426545 {A : Type'} : (term841 A) = (term841 A).
Proof. exact (eq_refl (term841 A)). Qed.
Lemma lem5426546 {A : Type'} (i : type661 A) (j : type661 A) : (term872 A i j) = (term873 A i j).
Proof. exact (MK_COMB (@lem5426544 A i j) (@lem5426545 A)). Qed.
Lemma lem5426547 {A : Type'} (i : type661 A) : (term874 A i) = (term875 A i).
Proof. exact (fun_ext (fun j : type661 A => @lem5426546 A i j)). Qed.
Lemma lem5426548 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426549 {A : Type'} (i : type661 A) : (term863 A i) = (term876 A i).
Proof. exact (MK_COMB (@lem5426548 A) (@lem5426547 A i)). Qed.
Lemma lem5426550 {A : Type'} (i : type661 A) : ((term862 A i) = (term863 A i)) = ((term858 A i) = (term876 A i)).
Proof. exact (MK_COMB (@lem5426541 A i) (@lem5426549 A i)). Qed.
Lemma lem5426551 {A : Type'} (i : type661 A) : (term858 A i) = (term876 A i).
Proof. exact (EQ_MP (@lem5426550 A i) (@lem5426531 A i)). Qed.
Lemma lem5426553 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5426554 {A : Type'} (P : Prop) (Q : type159 A) : (term877 A P Q) = (term878 A P Q).
Proof. exact (@lem5426553 (type681 A) P Q). Qed.
Lemma lem5426555 {A : Type'} (i : type661 A) (j : type661 A) : (term879 A i j) = (term880 A i j).
Proof. exact (@lem5426554 A (term798 A i j) (term840 A)). Qed.
Lemma lem5426556 {A : Type'} (f : type681 A) : (term881 A f) = (term838 A f).
Proof. exact (eq_refl (term881 A f)). Qed.
Lemma lem5426557 {A : Type'} : (term882 A) = (term840 A).
Proof. exact (fun_ext (fun f : type681 A => @lem5426556 A f)). Qed.
Lemma lem5426558 {A : Type'} : (@ex ((A -> Prop) -> nat -> A)) = (@ex ((A -> Prop) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> nat -> A))). Qed.
Lemma lem5426559 {A : Type'} : (term883 A) = (term841 A).
Proof. exact (MK_COMB (@lem5426558 A) (@lem5426557 A)). Qed.
Lemma lem5426560 {A : Type'} (i : type661 A) (j : type661 A) : (term871 A i j) = (term871 A i j).
Proof. exact (eq_refl (term871 A i j)). Qed.
Lemma lem5426561 {A : Type'} (i : type661 A) (j : type661 A) : (term879 A i j) = (term873 A i j).
Proof. exact (MK_COMB (@lem5426560 A i j) (@lem5426559 A)). Qed.
Lemma lem5426562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426563 {A : Type'} (i : type661 A) (j : type661 A) : (term884 A i j) = (term885 A i j).
Proof. exact (MK_COMB (@lem5426562) (@lem5426561 A i j)). Qed.
Lemma lem5426564 {A : Type'} (f : type681 A) : (term881 A f) = (term838 A f).
Proof. exact (eq_refl (term881 A f)). Qed.
Lemma lem5426565 {A : Type'} (i : type661 A) (j : type661 A) : (term871 A i j) = (term871 A i j).
Proof. exact (eq_refl (term871 A i j)). Qed.
Lemma lem5426566 {A : Type'} (i : type661 A) (j : type661 A) (f : type681 A) : (term886 A i j f) = (term887 A i j f).
Proof. exact (MK_COMB (@lem5426565 A i j) (@lem5426564 A f)). Qed.
Lemma lem5426567 {A : Type'} (i : type661 A) (j : type661 A) : (term888 A i j) = (term889 A i j).
Proof. exact (fun_ext (fun f : type681 A => @lem5426566 A i j f)). Qed.
Lemma lem5426568 {A : Type'} : (@ex ((A -> Prop) -> nat -> A)) = (@ex ((A -> Prop) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> nat -> A))). Qed.
Lemma lem5426569 {A : Type'} (i : type661 A) (j : type661 A) : (term880 A i j) = (term890 A i j).
Proof. exact (MK_COMB (@lem5426568 A) (@lem5426567 A i j)). Qed.
Lemma lem5426570 {A : Type'} (i : type661 A) (j : type661 A) : ((term879 A i j) = (term880 A i j)) = ((term873 A i j) = (term890 A i j)).
Proof. exact (MK_COMB (@lem5426563 A i j) (@lem5426569 A i j)). Qed.
Lemma lem5426571 {A : Type'} (i : type661 A) (j : type661 A) : (term873 A i j) = (term890 A i j).
Proof. exact (EQ_MP (@lem5426570 A i j) (@lem5426555 A i j)). Qed.
Lemma lem5426572 {A : Type'} (i : type661 A) : (term875 A i) = (term891 A i).
Proof. exact (fun_ext (fun j : type661 A => @lem5426571 A i j)). Qed.
Lemma lem5426573 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426574 {A : Type'} (i : type661 A) : (term876 A i) = (term892 A i).
Proof. exact (MK_COMB (@lem5426573 A) (@lem5426572 A i)). Qed.
Lemma lem5426575 {A : Type'} (i : type661 A) : (term858 A i) = (term892 A i).
Proof. exact (TRANS (@lem5426551 A i) (@lem5426574 A i)). Qed.
Lemma lem5426576 {A : Type'} : (term860 A) = (term893 A).
Proof. exact (fun_ext (fun i : type661 A => @lem5426575 A i)). Qed.
Lemma lem5426577 {A : Type'} : (@ex ((A -> Prop) -> (nat -> A) -> nat)) = (@ex ((A -> Prop) -> (nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (nat -> A) -> nat))). Qed.
Lemma lem5426578 {A : Type'} : (term861 A) = (term894 A).
Proof. exact (MK_COMB (@lem5426577 A) (@lem5426576 A)). Qed.
Lemma lem5426579 {A : Type'} : (term842 A) = (term894 A).
Proof. exact (TRANS (@lem5426527 A) (@lem5426578 A)). Qed.
Lemma lem5426580 {A : Type'} : (term644 A) = (term894 A).
Proof. exact (TRANS (@lem5426503 A) (@lem5426579 A)). Qed.
Lemma lem5426581 {A : Type'} : (term620 A) = (term894 A).
Proof. exact (TRANS (@lem5425935 A) (@lem5426580 A)). Qed.
Lemma lem5426582 {A : Type'} : (term11 A) = (term894 A).
Proof. exact (TRANS (@lem5425908 A) (@lem5426581 A)). Qed.
Lemma lem5426583 {A : Type'} (h1 : term11 A) : term894 A.
Proof. exact (EQ_MP (@lem5426582 A) (@lem5424290 A h1)). Qed.
Lemma lem5426596 {A : Type'} (s : type686 A) (i : nat) (f : type1597 A) (j : nat) : (term895 A s i f j) = (term896 A s i f j).
Proof. exact (@lem17045 (term897 A j s) ((f i) = (f j))). Qed.
Lemma lem5426601 {A : Type'} (i : nat) (s : type686 A) : (term898 A i s) = (term898 A i s).
Proof. exact (eq_refl (term898 A i s)). Qed.
Lemma lem5426602 {A : Type'} (s : type686 A) (i : nat) (f : type1597 A) (j : nat) : (term899 A s i f j) = (term900 A s i f j).
Proof. exact (MK_COMB (@lem5426601 A i s) (@lem5426596 A s i f j)). Qed.
Lemma lem5426603 {A : Type'} (s : type686 A) (i : nat) (f : type1597 A) (j : nat) : (term901 A s i f j) = (term899 A s i f j).
Proof. exact (@lem17045 (term897 A i s) (term902 A s i f j)). Qed.
Lemma lem5426604 {A : Type'} (s : type686 A) (i : nat) (f : type1597 A) (j : nat) : (term901 A s i f j) = (term900 A s i f j).
Proof. exact (TRANS (@lem5426603 A s i f j) (@lem5426602 A s i f j)). Qed.
Lemma lem5426609 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5426614 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term903 A s f i j) = (term904 A s f i j).
Proof. exact (@lem17362 (term905 A s i f j) (i = j)). Qed.
Lemma lem5426615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426616 {A : Type'} (s : type686 A) (i : nat) (f : type1597 A) (j : nat) : (term906 A s i f j) = (term907 A s i f j).
Proof. exact (MK_COMB (@lem5426615) (@lem5426604 A s i f j)). Qed.
Lemma lem5426617 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term908 A s f i j) = (term909 A s f i j).
Proof. exact (MK_COMB (@lem5426616 A s i f j) (@lem5426609 i j)). Qed.
Lemma lem5426618 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term78 A s f i j) = (term908 A s f i j).
Proof. exact (@lem17265 (term905 A s i f j) (i = j)). Qed.
Lemma lem5426619 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term78 A s f i j) = (term909 A s f i j).
Proof. exact (TRANS (@lem5426618 A s f i j) (@lem5426617 A s f i j)). Qed.
Lemma lem5426620 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5426621 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term910 A s f i) = (term911 A s f i).
Proof. exact (@lem5426620 (term79 A s f i)). Qed.
Lemma lem5426622 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term912 A s f i j) = (term78 A s f i j).
Proof. exact (eq_refl (term912 A s f i j)). Qed.
Lemma lem5426623 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5426624 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term913 A s f i j) = (term903 A s f i j).
Proof. exact (MK_COMB (@lem5426623) (@lem5426622 A s f i j)). Qed.
Lemma lem5426625 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term913 A s f i j) = (term904 A s f i j).
Proof. exact (TRANS (@lem5426624 A s f i j) (@lem5426614 A s f i j)). Qed.
Lemma lem5426626 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term914 A s f i) = (term915 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5426625 A s f i j)). Qed.
Lemma lem5426627 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426628 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term911 A s f i) = (term916 A s f i).
Proof. exact (MK_COMB (@lem5426627) (@lem5426626 A s f i)). Qed.
Lemma lem5426629 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term910 A s f i) = (term916 A s f i).
Proof. exact (TRANS (@lem5426621 A s f i) (@lem5426628 A s f i)). Qed.
Lemma lem5426630 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term79 A s f i) = (term917 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5426619 A s f i j)). Qed.
Lemma lem5426631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5426632 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term80 A s f i) = (term918 A s f i).
Proof. exact (MK_COMB (@lem5426631) (@lem5426630 A s f i)). Qed.
Lemma lem5426633 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5426634 {A : Type'} (s : type686 A) (f : type1597 A) : (term919 A s f) = (term920 A s f).
Proof. exact (@lem5426633 (term81 A s f)). Qed.
Lemma lem5426635 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term921 A s f i) = (term80 A s f i).
Proof. exact (eq_refl (term921 A s f i)). Qed.
Lemma lem5426636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5426637 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term922 A s f i) = (term910 A s f i).
Proof. exact (MK_COMB (@lem5426636) (@lem5426635 A s f i)). Qed.
Lemma lem5426638 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term922 A s f i) = (term916 A s f i).
Proof. exact (TRANS (@lem5426637 A s f i) (@lem5426629 A s f i)). Qed.
Lemma lem5426639 {A : Type'} (s : type686 A) (f : type1597 A) : (term923 A s f) = (term924 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5426638 A s f i)). Qed.
Lemma lem5426640 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426641 {A : Type'} (s : type686 A) (f : type1597 A) : (term920 A s f) = (term925 A s f).
Proof. exact (MK_COMB (@lem5426640) (@lem5426639 A s f)). Qed.
Lemma lem5426642 {A : Type'} (s : type686 A) (f : type1597 A) : (term919 A s f) = (term925 A s f).
Proof. exact (TRANS (@lem5426634 A s f) (@lem5426641 A s f)). Qed.
Lemma lem5426643 {A : Type'} (s : type686 A) (f : type1597 A) : (term81 A s f) = (term926 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5426632 A s f i)). Qed.
Lemma lem5426644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5426645 {A : Type'} (s : type686 A) (f : type1597 A) : (term82 A s f) = (term927 A s f).
Proof. exact (MK_COMB (@lem5426644) (@lem5426643 A s f)). Qed.
Lemma lem5426646 {A : Type'} (f : type1597 A) (s : type686 A) : (term928 A f s) = (term928 A f s).
Proof. exact (eq_refl (term928 A f s)). Qed.
Lemma lem5426647 {A : Type'} (f : type1597 A) (s : type686 A) : (s = (term77 A f s)) = (s = (term77 A f s)).
Proof. exact (eq_refl (s = (term77 A f s))). Qed.
Lemma lem5426648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426649 {A : Type'} (s : type686 A) (f : type1597 A) : (term929 A s f) = (term930 A s f).
Proof. exact (MK_COMB (@lem5426648) (@lem5426642 A s f)). Qed.
Lemma lem5426650 {A : Type'} (f : type1597 A) (s : type686 A) : (term931 A f s) = (term932 A f s).
Proof. exact (MK_COMB (@lem5426649 A s f) (@lem5426646 A f s)). Qed.
Lemma lem5426651 {A : Type'} (f : type1597 A) (s : type686 A) : (term933 A f s) = (term931 A f s).
Proof. exact (@lem17045 (term82 A s f) (s = (term77 A f s))). Qed.
Lemma lem5426652 {A : Type'} (f : type1597 A) (s : type686 A) : (term933 A f s) = (term932 A f s).
Proof. exact (TRANS (@lem5426651 A f s) (@lem5426650 A f s)). Qed.
Lemma lem5426653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426654 {A : Type'} (s : type686 A) (f : type1597 A) : (term83 A s f) = (term934 A s f).
Proof. exact (MK_COMB (@lem5426653) (@lem5426645 A s f)). Qed.
Lemma lem5426655 {A : Type'} (f : type1597 A) (s : type686 A) : (term84 A f s) = (term935 A f s).
Proof. exact (MK_COMB (@lem5426654 A s f) (@lem5426647 A f s)). Qed.
Lemma lem5426656 {A : Type'} (P : type953 A) : (term936 A P) = (term937 A P).
Proof. exact (@lem18394 (type1597 A) P). Qed.
Lemma lem5426657 {A : Type'} (s : type686 A) : (term938 A s) = (term939 A s).
Proof. exact (@lem5426656 A (term85 A s)). Qed.
Lemma lem5426658 {A : Type'} (f : type1597 A) (s : type686 A) : (term940 A s f) = (term84 A f s).
Proof. exact (eq_refl (term940 A s f)). Qed.
Lemma lem5426659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5426660 {A : Type'} (f : type1597 A) (s : type686 A) : (term941 A s f) = (term933 A f s).
Proof. exact (MK_COMB (@lem5426659) (@lem5426658 A f s)). Qed.
Lemma lem5426661 {A : Type'} (f : type1597 A) (s : type686 A) : (term941 A s f) = (term932 A f s).
Proof. exact (TRANS (@lem5426660 A f s) (@lem5426652 A f s)). Qed.
Lemma lem5426662 {A : Type'} (s : type686 A) : (term942 A s) = (term943 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5426661 A f s)). Qed.
Lemma lem5426663 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5426664 {A : Type'} (s : type686 A) : (term939 A s) = (term944 A s).
Proof. exact (MK_COMB (@lem5426663 A) (@lem5426662 A s)). Qed.
Lemma lem5426665 {A : Type'} (s : type686 A) : (term938 A s) = (term944 A s).
Proof. exact (TRANS (@lem5426657 A s) (@lem5426664 A s)). Qed.
Lemma lem5426666 {A : Type'} (s : type686 A) : (term85 A s) = (term945 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5426655 A f s)). Qed.
Lemma lem5426667 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem5426668 {A : Type'} (s : type686 A) : (term86 A s) = (term946 A s).
Proof. exact (MK_COMB (@lem5426667 A) (@lem5426666 A s)). Qed.
Lemma lem5426670 {A : Type'} (s : type686 A) : (term947 A s) = (term947 A s).
Proof. exact (eq_refl (term947 A s)). Qed.
Lemma lem5426671 {A : Type'} (s : type686 A) : (term948 A s) = (term949 A s).
Proof. exact (MK_COMB (@lem5426670 A s) (@lem5426668 A s)). Qed.
Lemma lem5426673 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5426674 {A : Type'} (s : type686 A) : (term951 A s) = (term952 A s).
Proof. exact (MK_COMB (@lem5426673 A s) (@lem5426665 A s)). Qed.
Lemma lem5426675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426676 {A : Type'} (s : type686 A) : (term953 A s) = (term954 A s).
Proof. exact (MK_COMB (@lem5426675) (@lem5426674 A s)). Qed.
Lemma lem5426677 {A : Type'} (s : type686 A) : (term955 A s) = (term956 A s).
Proof. exact (MK_COMB (@lem5426676 A s) (@lem5426671 A s)). Qed.
Lemma lem5426678 {A : Type'} (s : type686 A) : ((@FINITE (A -> Prop) s) = (term86 A s)) = (term955 A s).
Proof. exact (@lem17784 (@FINITE (A -> Prop) s) (term86 A s)). Qed.
Lemma lem5426679 {A : Type'} (s : type686 A) : ((@FINITE (A -> Prop) s) = (term86 A s)) = (term956 A s).
Proof. exact (TRANS (@lem5426678 A s) (@lem5426677 A s)). Qed.
Lemma lem5426680 {A : Type'} : (term88 A) = (term957 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5426679 A s)). Qed.
Lemma lem5426681 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5426682 {A : Type'} : (term13 A) = (term958 A).
Proof. exact (MK_COMB (@lem5426681 A) (@lem5426680 A)). Qed.
Lemma lem5426684 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5426685 {A : Type'} (P : type180 A) (Q : type180 A) : (term959 A P Q) = (term960 A P Q).
Proof. exact (@lem5426684 (type686 A) P Q). Qed.
Lemma lem5426686 {A : Type'} : (term961 A) = (term962 A).
Proof. exact (@lem5426685 A (term963 A) (term964 A)). Qed.
Lemma lem5426687 {A : Type'} (s : type686 A) : (term965 A s) = (term952 A s).
Proof. exact (eq_refl (term965 A s)). Qed.
Lemma lem5426688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426689 {A : Type'} (s : type686 A) : (term966 A s) = (term954 A s).
Proof. exact (MK_COMB (@lem5426688) (@lem5426687 A s)). Qed.
Lemma lem5426690 {A : Type'} (s : type686 A) : (term967 A s) = (term949 A s).
Proof. exact (eq_refl (term967 A s)). Qed.
Lemma lem5426691 {A : Type'} (s : type686 A) : (term968 A s) = (term956 A s).
Proof. exact (MK_COMB (@lem5426689 A s) (@lem5426690 A s)). Qed.
Lemma lem5426692 {A : Type'} : (term969 A) = (term957 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5426691 A s)). Qed.
Lemma lem5426693 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5426694 {A : Type'} : (term961 A) = (term958 A).
Proof. exact (MK_COMB (@lem5426693 A) (@lem5426692 A)). Qed.
Lemma lem5426695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426696 {A : Type'} : (term970 A) = (term971 A).
Proof. exact (MK_COMB (@lem5426695) (@lem5426694 A)). Qed.
Lemma lem5426697 {A : Type'} (s : type686 A) : (term965 A s) = (term952 A s).
Proof. exact (eq_refl (term965 A s)). Qed.
Lemma lem5426698 {A : Type'} : (term972 A) = (term963 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5426697 A s)). Qed.
Lemma lem5426699 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5426700 {A : Type'} : (term973 A) = (term974 A).
Proof. exact (MK_COMB (@lem5426699 A) (@lem5426698 A)). Qed.
Lemma lem5426701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5426702 {A : Type'} : (term975 A) = (term976 A).
Proof. exact (MK_COMB (@lem5426701) (@lem5426700 A)). Qed.
Lemma lem5426703 {A : Type'} (s : type686 A) : (term967 A s) = (term949 A s).
Proof. exact (eq_refl (term967 A s)). Qed.
Lemma lem5426704 {A : Type'} : (term977 A) = (term964 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5426703 A s)). Qed.
Lemma lem5426705 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5426706 {A : Type'} : (term978 A) = (term979 A).
Proof. exact (MK_COMB (@lem5426705 A) (@lem5426704 A)). Qed.
Lemma lem5426707 {A : Type'} : (term962 A) = (term980 A).
Proof. exact (MK_COMB (@lem5426702 A) (@lem5426706 A)). Qed.
Lemma lem5426708 {A : Type'} : ((term961 A) = (term962 A)) = ((term958 A) = (term980 A)).
Proof. exact (MK_COMB (@lem5426696 A) (@lem5426707 A)). Qed.
Lemma lem5426709 {A : Type'} : (term958 A) = (term980 A).
Proof. exact (EQ_MP (@lem5426708 A) (@lem5426686 A)). Qed.
Lemma lem5426987 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5426988 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5426987 nat P Q). Qed.
Lemma lem5426989 {A : Type'} (f : type1597 A) (s : type686 A) : (term981 A f s) = (term982 A f s).
Proof. exact (@lem5426988 (term924 A s f) (term928 A f s)). Qed.
Lemma lem5426990 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term983 A s f i) = (term916 A s f i).
Proof. exact (eq_refl (term983 A s f i)). Qed.
Lemma lem5426991 {A : Type'} (s : type686 A) (f : type1597 A) : (term984 A s f) = (term924 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5426990 A s f i)). Qed.
Lemma lem5426992 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5426993 {A : Type'} (s : type686 A) (f : type1597 A) : (term985 A s f) = (term925 A s f).
Proof. exact (MK_COMB (@lem5426992) (@lem5426991 A s f)). Qed.
Lemma lem5426994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5426995 {A : Type'} (s : type686 A) (f : type1597 A) : (term986 A s f) = (term930 A s f).
Proof. exact (MK_COMB (@lem5426994) (@lem5426993 A s f)). Qed.
Lemma lem5426996 {A : Type'} (f : type1597 A) (s : type686 A) : (term928 A f s) = (term928 A f s).
Proof. exact (eq_refl (term928 A f s)). Qed.
Lemma lem5426997 {A : Type'} (f : type1597 A) (s : type686 A) : (term981 A f s) = (term932 A f s).
Proof. exact (MK_COMB (@lem5426995 A s f) (@lem5426996 A f s)). Qed.
Lemma lem5426998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5426999 {A : Type'} (f : type1597 A) (s : type686 A) : (term987 A f s) = (term988 A f s).
Proof. exact (MK_COMB (@lem5426998) (@lem5426997 A f s)). Qed.
Lemma lem5427000 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term983 A s f i) = (term916 A s f i).
Proof. exact (eq_refl (term983 A s f i)). Qed.
Lemma lem5427001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427002 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term989 A s f i) = (term990 A s f i).
Proof. exact (MK_COMB (@lem5427001) (@lem5427000 A s f i)). Qed.
Lemma lem5427003 {A : Type'} (f : type1597 A) (s : type686 A) : (term928 A f s) = (term928 A f s).
Proof. exact (eq_refl (term928 A f s)). Qed.
Lemma lem5427004 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term991 A i f s) = (term992 A i f s).
Proof. exact (MK_COMB (@lem5427002 A s f i) (@lem5427003 A f s)). Qed.
Lemma lem5427005 {A : Type'} (f : type1597 A) (s : type686 A) : (term993 A f s) = (term994 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5427004 A i f s)). Qed.
Lemma lem5427006 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427007 {A : Type'} (f : type1597 A) (s : type686 A) : (term982 A f s) = (term995 A f s).
Proof. exact (MK_COMB (@lem5427006) (@lem5427005 A f s)). Qed.
Lemma lem5427008 {A : Type'} (f : type1597 A) (s : type686 A) : ((term981 A f s) = (term982 A f s)) = ((term932 A f s) = (term995 A f s)).
Proof. exact (MK_COMB (@lem5426999 A f s) (@lem5427007 A f s)). Qed.
Lemma lem5427009 {A : Type'} (f : type1597 A) (s : type686 A) : (term932 A f s) = (term995 A f s).
Proof. exact (EQ_MP (@lem5427008 A f s) (@lem5426989 A f s)). Qed.
Lemma lem5427011 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5427012 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5427011 nat P Q). Qed.
Lemma lem5427013 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term996 A i f s) = (term997 A i f s).
Proof. exact (@lem5427012 (term915 A s f i) (term928 A f s)). Qed.
Lemma lem5427014 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term998 A s f i j) = (term904 A s f i j).
Proof. exact (eq_refl (term998 A s f i j)). Qed.
Lemma lem5427015 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term999 A s f i) = (term915 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5427014 A s f i j)). Qed.
Lemma lem5427016 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427017 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term1000 A s f i) = (term916 A s f i).
Proof. exact (MK_COMB (@lem5427016) (@lem5427015 A s f i)). Qed.
Lemma lem5427018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427019 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) : (term1001 A s f i) = (term990 A s f i).
Proof. exact (MK_COMB (@lem5427018) (@lem5427017 A s f i)). Qed.
Lemma lem5427020 {A : Type'} (f : type1597 A) (s : type686 A) : (term928 A f s) = (term928 A f s).
Proof. exact (eq_refl (term928 A f s)). Qed.
Lemma lem5427021 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term996 A i f s) = (term992 A i f s).
Proof. exact (MK_COMB (@lem5427019 A s f i) (@lem5427020 A f s)). Qed.
Lemma lem5427022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427023 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term1002 A i f s) = (term1003 A i f s).
Proof. exact (MK_COMB (@lem5427022) (@lem5427021 A i f s)). Qed.
Lemma lem5427024 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term998 A s f i j) = (term904 A s f i j).
Proof. exact (eq_refl (term998 A s f i j)). Qed.
Lemma lem5427025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427026 {A : Type'} (s : type686 A) (f : type1597 A) (i : nat) (j : nat) : (term1004 A s f i j) = (term1005 A s f i j).
Proof. exact (MK_COMB (@lem5427025) (@lem5427024 A s f i j)). Qed.
Lemma lem5427027 {A : Type'} (f : type1597 A) (s : type686 A) : (term928 A f s) = (term928 A f s).
Proof. exact (eq_refl (term928 A f s)). Qed.
Lemma lem5427028 {A : Type'} (i : nat) (j : nat) (f : type1597 A) (s : type686 A) : (term1006 A i j f s) = (term1007 A i j f s).
Proof. exact (MK_COMB (@lem5427026 A s f i j) (@lem5427027 A f s)). Qed.
Lemma lem5427029 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term1008 A i f s) = (term1009 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5427028 A i j f s)). Qed.
Lemma lem5427030 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427031 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term997 A i f s) = (term1010 A i f s).
Proof. exact (MK_COMB (@lem5427030) (@lem5427029 A i f s)). Qed.
Lemma lem5427032 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : ((term996 A i f s) = (term997 A i f s)) = ((term992 A i f s) = (term1010 A i f s)).
Proof. exact (MK_COMB (@lem5427023 A i f s) (@lem5427031 A i f s)). Qed.
Lemma lem5427033 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term992 A i f s) = (term1010 A i f s).
Proof. exact (EQ_MP (@lem5427032 A i f s) (@lem5427013 A i f s)). Qed.
Lemma lem5427034 {A : Type'} (f : type1597 A) (s : type686 A) : (term994 A f s) = (term1011 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5427033 A i f s)). Qed.
Lemma lem5427035 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427036 {A : Type'} (f : type1597 A) (s : type686 A) : (term995 A f s) = (term1012 A f s).
Proof. exact (MK_COMB (@lem5427035) (@lem5427034 A f s)). Qed.
Lemma lem5427037 {A : Type'} (f : type1597 A) (s : type686 A) : (term932 A f s) = (term1012 A f s).
Proof. exact (TRANS (@lem5427009 A f s) (@lem5427036 A f s)). Qed.
Lemma lem5427038 {A : Type'} (s : type686 A) : (term943 A s) = (term1013 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427037 A f s)). Qed.
Lemma lem5427039 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5427040 {A : Type'} (s : type686 A) : (term944 A s) = (term1014 A s).
Proof. exact (MK_COMB (@lem5427039 A) (@lem5427038 A s)). Qed.
Lemma lem5427042 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427043 {A : Type'} (P : type952 A) : (term1015 A P) = (term1016 A P).
Proof. exact (@lem5427042 (type1597 A) nat P). Qed.
Lemma lem5427044 {A : Type'} (s : type686 A) : (term1017 A s) = (term1018 A s).
Proof. exact (@lem5427043 A (term1019 A s)). Qed.
Lemma lem5427045 {A : Type'} (f : type1597 A) (s : type686 A) : (term1020 A s f) = (term1011 A f s).
Proof. exact (eq_refl (term1020 A s f)). Qed.
Lemma lem5427046 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5427047 {A : Type'} (f : type1597 A) (s : type686 A) (i : nat) : (term1021 A s f i) = (term1022 A f s i).
Proof. exact (MK_COMB (@lem5427045 A f s) (@lem5427046 i)). Qed.
Lemma lem5427048 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term1022 A f s i) = (term1010 A i f s).
Proof. exact (eq_refl (term1022 A f s i)). Qed.
Lemma lem5427049 {A : Type'} (i : nat) (f : type1597 A) (s : type686 A) : (term1021 A s f i) = (term1010 A i f s).
Proof. exact (TRANS (@lem5427047 A f s i) (@lem5427048 A i f s)). Qed.
Lemma lem5427050 {A : Type'} (f : type1597 A) (s : type686 A) : (term1023 A s f) = (term1011 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5427049 A i f s)). Qed.
Lemma lem5427051 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427052 {A : Type'} (f : type1597 A) (s : type686 A) : (term1024 A s f) = (term1012 A f s).
Proof. exact (MK_COMB (@lem5427051) (@lem5427050 A f s)). Qed.
Lemma lem5427053 {A : Type'} (s : type686 A) : (term1025 A s) = (term1013 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427052 A f s)). Qed.
Lemma lem5427054 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5427055 {A : Type'} (s : type686 A) : (term1017 A s) = (term1014 A s).
Proof. exact (MK_COMB (@lem5427054 A) (@lem5427053 A s)). Qed.
Lemma lem5427056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427057 {A : Type'} (s : type686 A) : (term1026 A s) = (term1027 A s).
Proof. exact (MK_COMB (@lem5427056) (@lem5427055 A s)). Qed.
Lemma lem5427058 {A : Type'} (f : type1597 A) (s : type686 A) : (term1020 A s f) = (term1011 A f s).
Proof. exact (eq_refl (term1020 A s f)). Qed.
Lemma lem5427059 {A : Type'} (i : type954 A) (f : type1597 A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem5427060 {A : Type'} (s : type686 A) (i : type954 A) (f : type1597 A) : (term1028 A s i f) = (term1029 A s i f).
Proof. exact (MK_COMB (@lem5427058 A f s) (@lem5427059 A i f)). Qed.
Lemma lem5427061 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1029 A s i f) = (term1030 A i f s).
Proof. exact (eq_refl (term1029 A s i f)). Qed.
Lemma lem5427062 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1028 A s i f) = (term1030 A i f s).
Proof. exact (TRANS (@lem5427060 A s i f) (@lem5427061 A i f s)). Qed.
Lemma lem5427063 {A : Type'} (i : type954 A) (s : type686 A) : (term1031 A s i) = (term1032 A i s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427062 A i f s)). Qed.
Lemma lem5427064 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5427065 {A : Type'} (i : type954 A) (s : type686 A) : (term1033 A s i) = (term1034 A i s).
Proof. exact (MK_COMB (@lem5427064 A) (@lem5427063 A i s)). Qed.
Lemma lem5427066 {A : Type'} (s : type686 A) : (term1035 A s) = (term1036 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427065 A i s)). Qed.
Lemma lem5427067 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427068 {A : Type'} (s : type686 A) : (term1018 A s) = (term1037 A s).
Proof. exact (MK_COMB (@lem5427067 A) (@lem5427066 A s)). Qed.
Lemma lem5427069 {A : Type'} (s : type686 A) : ((term1017 A s) = (term1018 A s)) = ((term1014 A s) = (term1037 A s)).
Proof. exact (MK_COMB (@lem5427057 A s) (@lem5427068 A s)). Qed.
Lemma lem5427070 {A : Type'} (s : type686 A) : (term1014 A s) = (term1037 A s).
Proof. exact (EQ_MP (@lem5427069 A s) (@lem5427044 A s)). Qed.
Lemma lem5427072 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427073 {A : Type'} (P : type952 A) : (term1015 A P) = (term1016 A P).
Proof. exact (@lem5427072 (type1597 A) nat P). Qed.
Lemma lem5427074 {A : Type'} (i : type954 A) (s : type686 A) : (term1038 A i s) = (term1039 A i s).
Proof. exact (@lem5427073 A (term1040 A i s)). Qed.
Lemma lem5427075 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1041 A i s f) = (term1042 A i f s).
Proof. exact (eq_refl (term1041 A i s f)). Qed.
Lemma lem5427076 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5427077 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) (j : nat) : (term1043 A i s f j) = (term1044 A i f s j).
Proof. exact (MK_COMB (@lem5427075 A i f s) (@lem5427076 j)). Qed.
Lemma lem5427078 {A : Type'} (i : type954 A) (j : nat) (f : type1597 A) (s : type686 A) : (term1044 A i f s j) = (term1045 A i j f s).
Proof. exact (eq_refl (term1044 A i f s j)). Qed.
Lemma lem5427079 {A : Type'} (i : type954 A) (j : nat) (f : type1597 A) (s : type686 A) : (term1043 A i s f j) = (term1045 A i j f s).
Proof. exact (TRANS (@lem5427077 A i f s j) (@lem5427078 A i j f s)). Qed.
Lemma lem5427080 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1046 A i s f) = (term1042 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5427079 A i j f s)). Qed.
Lemma lem5427081 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427082 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1047 A i s f) = (term1030 A i f s).
Proof. exact (MK_COMB (@lem5427081) (@lem5427080 A i f s)). Qed.
Lemma lem5427083 {A : Type'} (i : type954 A) (s : type686 A) : (term1048 A i s) = (term1032 A i s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427082 A i f s)). Qed.
Lemma lem5427084 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5427085 {A : Type'} (i : type954 A) (s : type686 A) : (term1038 A i s) = (term1034 A i s).
Proof. exact (MK_COMB (@lem5427084 A) (@lem5427083 A i s)). Qed.
Lemma lem5427086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427087 {A : Type'} (i : type954 A) (s : type686 A) : (term1049 A i s) = (term1050 A i s).
Proof. exact (MK_COMB (@lem5427086) (@lem5427085 A i s)). Qed.
Lemma lem5427088 {A : Type'} (i : type954 A) (f : type1597 A) (s : type686 A) : (term1041 A i s f) = (term1042 A i f s).
Proof. exact (eq_refl (term1041 A i s f)). Qed.
Lemma lem5427089 {A : Type'} (j : type954 A) (f : type1597 A) : (j f) = (j f).
Proof. exact (eq_refl (j f)). Qed.
Lemma lem5427090 {A : Type'} (i : type954 A) (s : type686 A) (j : type954 A) (f : type1597 A) : (term1051 A i s j f) = (term1052 A i s j f).
Proof. exact (MK_COMB (@lem5427088 A i f s) (@lem5427089 A j f)). Qed.
Lemma lem5427091 {A : Type'} (i : type954 A) (j : type954 A) (f : type1597 A) (s : type686 A) : (term1052 A i s j f) = (term1053 A i j f s).
Proof. exact (eq_refl (term1052 A i s j f)). Qed.
Lemma lem5427092 {A : Type'} (i : type954 A) (j : type954 A) (f : type1597 A) (s : type686 A) : (term1051 A i s j f) = (term1053 A i j f s).
Proof. exact (TRANS (@lem5427090 A i s j f) (@lem5427091 A i j f s)). Qed.
Lemma lem5427093 {A : Type'} (i : type954 A) (j : type954 A) (s : type686 A) : (term1054 A i s j) = (term1055 A i j s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427092 A i j f s)). Qed.
Lemma lem5427094 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem5427095 {A : Type'} (i : type954 A) (j : type954 A) (s : type686 A) : (term1056 A i s j) = (term1057 A i j s).
Proof. exact (MK_COMB (@lem5427094 A) (@lem5427093 A i j s)). Qed.
Lemma lem5427096 {A : Type'} (i : type954 A) (s : type686 A) : (term1058 A i s) = (term1059 A i s).
Proof. exact (fun_ext (fun j : type954 A => @lem5427095 A i j s)). Qed.
Lemma lem5427097 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427098 {A : Type'} (i : type954 A) (s : type686 A) : (term1039 A i s) = (term1060 A i s).
Proof. exact (MK_COMB (@lem5427097 A) (@lem5427096 A i s)). Qed.
Lemma lem5427099 {A : Type'} (i : type954 A) (s : type686 A) : ((term1038 A i s) = (term1039 A i s)) = ((term1034 A i s) = (term1060 A i s)).
Proof. exact (MK_COMB (@lem5427087 A i s) (@lem5427098 A i s)). Qed.
Lemma lem5427100 {A : Type'} (i : type954 A) (s : type686 A) : (term1034 A i s) = (term1060 A i s).
Proof. exact (EQ_MP (@lem5427099 A i s) (@lem5427074 A i s)). Qed.
Lemma lem5427101 {A : Type'} (s : type686 A) : (term1036 A s) = (term1061 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427100 A i s)). Qed.
Lemma lem5427102 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427103 {A : Type'} (s : type686 A) : (term1037 A s) = (term1062 A s).
Proof. exact (MK_COMB (@lem5427102 A) (@lem5427101 A s)). Qed.
Lemma lem5427104 {A : Type'} (s : type686 A) : (term1014 A s) = (term1062 A s).
Proof. exact (TRANS (@lem5427070 A s) (@lem5427103 A s)). Qed.
Lemma lem5427105 {A : Type'} (s : type686 A) : (term944 A s) = (term1062 A s).
Proof. exact (TRANS (@lem5427040 A s) (@lem5427104 A s)). Qed.
Lemma lem5427106 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5427107 {A : Type'} (s : type686 A) : (term952 A s) = (term1063 A s).
Proof. exact (MK_COMB (@lem5427106 A s) (@lem5427105 A s)). Qed.
Lemma lem5427109 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427110 {A : Type'} (P : Prop) (Q : type242 A) : (term1064 A P Q) = (term1065 A P Q).
Proof. exact (@lem5427109 (type954 A) P Q). Qed.
Lemma lem5427111 {A : Type'} (s : type686 A) : (term1066 A s) = (term1067 A s).
Proof. exact (@lem5427110 A (@FINITE (A -> Prop) s) (term1061 A s)). Qed.
Lemma lem5427112 {A : Type'} (i : type954 A) (s : type686 A) : (term1068 A s i) = (term1060 A i s).
Proof. exact (eq_refl (term1068 A s i)). Qed.
Lemma lem5427113 {A : Type'} (s : type686 A) : (term1069 A s) = (term1061 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427112 A i s)). Qed.
Lemma lem5427114 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427115 {A : Type'} (s : type686 A) : (term1070 A s) = (term1062 A s).
Proof. exact (MK_COMB (@lem5427114 A) (@lem5427113 A s)). Qed.
Lemma lem5427116 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5427117 {A : Type'} (s : type686 A) : (term1066 A s) = (term1063 A s).
Proof. exact (MK_COMB (@lem5427116 A s) (@lem5427115 A s)). Qed.
Lemma lem5427118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427119 {A : Type'} (s : type686 A) : (term1071 A s) = (term1072 A s).
Proof. exact (MK_COMB (@lem5427118) (@lem5427117 A s)). Qed.
Lemma lem5427120 {A : Type'} (i : type954 A) (s : type686 A) : (term1068 A s i) = (term1060 A i s).
Proof. exact (eq_refl (term1068 A s i)). Qed.
Lemma lem5427121 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5427122 {A : Type'} (i : type954 A) (s : type686 A) : (term1073 A s i) = (term1074 A i s).
Proof. exact (MK_COMB (@lem5427121 A s) (@lem5427120 A i s)). Qed.
Lemma lem5427123 {A : Type'} (s : type686 A) : (term1075 A s) = (term1076 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427122 A i s)). Qed.
Lemma lem5427124 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427125 {A : Type'} (s : type686 A) : (term1067 A s) = (term1077 A s).
Proof. exact (MK_COMB (@lem5427124 A) (@lem5427123 A s)). Qed.
Lemma lem5427126 {A : Type'} (s : type686 A) : ((term1066 A s) = (term1067 A s)) = ((term1063 A s) = (term1077 A s)).
Proof. exact (MK_COMB (@lem5427119 A s) (@lem5427125 A s)). Qed.
Lemma lem5427127 {A : Type'} (s : type686 A) : (term1063 A s) = (term1077 A s).
Proof. exact (EQ_MP (@lem5427126 A s) (@lem5427111 A s)). Qed.
Lemma lem5427129 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427130 {A : Type'} (P : Prop) (Q : type242 A) : (term1064 A P Q) = (term1065 A P Q).
Proof. exact (@lem5427129 (type954 A) P Q). Qed.
Lemma lem5427131 {A : Type'} (i : type954 A) (s : type686 A) : (term1078 A i s) = (term1079 A i s).
Proof. exact (@lem5427130 A (@FINITE (A -> Prop) s) (term1059 A i s)). Qed.
Lemma lem5427132 {A : Type'} (i : type954 A) (j : type954 A) (s : type686 A) : (term1080 A i s j) = (term1057 A i j s).
Proof. exact (eq_refl (term1080 A i s j)). Qed.
Lemma lem5427133 {A : Type'} (i : type954 A) (s : type686 A) : (term1081 A i s) = (term1059 A i s).
Proof. exact (fun_ext (fun j : type954 A => @lem5427132 A i j s)). Qed.
Lemma lem5427134 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427135 {A : Type'} (i : type954 A) (s : type686 A) : (term1082 A i s) = (term1060 A i s).
Proof. exact (MK_COMB (@lem5427134 A) (@lem5427133 A i s)). Qed.
Lemma lem5427136 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5427137 {A : Type'} (i : type954 A) (s : type686 A) : (term1078 A i s) = (term1074 A i s).
Proof. exact (MK_COMB (@lem5427136 A s) (@lem5427135 A i s)). Qed.
Lemma lem5427138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427139 {A : Type'} (i : type954 A) (s : type686 A) : (term1083 A i s) = (term1084 A i s).
Proof. exact (MK_COMB (@lem5427138) (@lem5427137 A i s)). Qed.
Lemma lem5427140 {A : Type'} (i : type954 A) (j : type954 A) (s : type686 A) : (term1080 A i s j) = (term1057 A i j s).
Proof. exact (eq_refl (term1080 A i s j)). Qed.
Lemma lem5427141 {A : Type'} (s : type686 A) : (term950 A s) = (term950 A s).
Proof. exact (eq_refl (term950 A s)). Qed.
Lemma lem5427142 {A : Type'} (i : type954 A) (j : type954 A) (s : type686 A) : (term1085 A i s j) = (term1086 A i j s).
Proof. exact (MK_COMB (@lem5427141 A s) (@lem5427140 A i j s)). Qed.
Lemma lem5427143 {A : Type'} (i : type954 A) (s : type686 A) : (term1087 A i s) = (term1088 A i s).
Proof. exact (fun_ext (fun j : type954 A => @lem5427142 A i j s)). Qed.
Lemma lem5427144 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427145 {A : Type'} (i : type954 A) (s : type686 A) : (term1079 A i s) = (term1089 A i s).
Proof. exact (MK_COMB (@lem5427144 A) (@lem5427143 A i s)). Qed.
Lemma lem5427146 {A : Type'} (i : type954 A) (s : type686 A) : ((term1078 A i s) = (term1079 A i s)) = ((term1074 A i s) = (term1089 A i s)).
Proof. exact (MK_COMB (@lem5427139 A i s) (@lem5427145 A i s)). Qed.
Lemma lem5427147 {A : Type'} (i : type954 A) (s : type686 A) : (term1074 A i s) = (term1089 A i s).
Proof. exact (EQ_MP (@lem5427146 A i s) (@lem5427131 A i s)). Qed.
Lemma lem5427148 {A : Type'} (s : type686 A) : (term1076 A s) = (term1090 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427147 A i s)). Qed.
Lemma lem5427149 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427150 {A : Type'} (s : type686 A) : (term1077 A s) = (term1091 A s).
Proof. exact (MK_COMB (@lem5427149 A) (@lem5427148 A s)). Qed.
Lemma lem5427151 {A : Type'} (s : type686 A) : (term1063 A s) = (term1091 A s).
Proof. exact (TRANS (@lem5427127 A s) (@lem5427150 A s)). Qed.
Lemma lem5427152 {A : Type'} (s : type686 A) : (term952 A s) = (term1091 A s).
Proof. exact (TRANS (@lem5427107 A s) (@lem5427151 A s)). Qed.
Lemma lem5427153 {A : Type'} : (term963 A) = (term1092 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5427152 A s)). Qed.
Lemma lem5427154 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427155 {A : Type'} : (term974 A) = (term1093 A).
Proof. exact (MK_COMB (@lem5427154 A) (@lem5427153 A)). Qed.
Lemma lem5427157 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427158 {A : Type'} (P : type172 A) : (term1094 A P) = (term1095 A P).
Proof. exact (@lem5427157 (type686 A) (type954 A) P). Qed.
Lemma lem5427159 {A : Type'} : (term1096 A) = (term1097 A).
Proof. exact (@lem5427158 A (term1098 A)). Qed.
Lemma lem5427160 {A : Type'} (s : type686 A) : (term1099 A s) = (term1090 A s).
Proof. exact (eq_refl (term1099 A s)). Qed.
Lemma lem5427161 {A : Type'} (i : type954 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5427162 {A : Type'} (s : type686 A) (i : type954 A) : (term1100 A s i) = (term1101 A s i).
Proof. exact (MK_COMB (@lem5427160 A s) (@lem5427161 A i)). Qed.
Lemma lem5427163 {A : Type'} (i : type954 A) (s : type686 A) : (term1101 A s i) = (term1089 A i s).
Proof. exact (eq_refl (term1101 A s i)). Qed.
Lemma lem5427164 {A : Type'} (i : type954 A) (s : type686 A) : (term1100 A s i) = (term1089 A i s).
Proof. exact (TRANS (@lem5427162 A s i) (@lem5427163 A i s)). Qed.
Lemma lem5427165 {A : Type'} (s : type686 A) : (term1102 A s) = (term1090 A s).
Proof. exact (fun_ext (fun i : type954 A => @lem5427164 A i s)). Qed.
Lemma lem5427166 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427167 {A : Type'} (s : type686 A) : (term1103 A s) = (term1091 A s).
Proof. exact (MK_COMB (@lem5427166 A) (@lem5427165 A s)). Qed.
Lemma lem5427168 {A : Type'} : (term1104 A) = (term1092 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5427167 A s)). Qed.
Lemma lem5427169 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427170 {A : Type'} : (term1096 A) = (term1093 A).
Proof. exact (MK_COMB (@lem5427169 A) (@lem5427168 A)). Qed.
Lemma lem5427171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427172 {A : Type'} : (term1105 A) = (term1106 A).
Proof. exact (MK_COMB (@lem5427171) (@lem5427170 A)). Qed.
Lemma lem5427173 {A : Type'} (s : type686 A) : (term1099 A s) = (term1090 A s).
Proof. exact (eq_refl (term1099 A s)). Qed.
Lemma lem5427174 {A : Type'} (i : type177 A) (s : type686 A) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem5427175 {A : Type'} (i : type177 A) (s : type686 A) : (term1107 A i s) = (term1108 A i s).
Proof. exact (MK_COMB (@lem5427173 A s) (@lem5427174 A i s)). Qed.
Lemma lem5427176 {A : Type'} (i : type177 A) (s : type686 A) : (term1108 A i s) = (term1109 A i s).
Proof. exact (eq_refl (term1108 A i s)). Qed.
Lemma lem5427177 {A : Type'} (i : type177 A) (s : type686 A) : (term1107 A i s) = (term1109 A i s).
Proof. exact (TRANS (@lem5427175 A i s) (@lem5427176 A i s)). Qed.
Lemma lem5427178 {A : Type'} (i : type177 A) : (term1110 A i) = (term1111 A i).
Proof. exact (fun_ext (fun s : type686 A => @lem5427177 A i s)). Qed.
Lemma lem5427179 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427180 {A : Type'} (i : type177 A) : (term1112 A i) = (term1113 A i).
Proof. exact (MK_COMB (@lem5427179 A) (@lem5427178 A i)). Qed.
Lemma lem5427181 {A : Type'} : (term1114 A) = (term1115 A).
Proof. exact (fun_ext (fun i : type177 A => @lem5427180 A i)). Qed.
Lemma lem5427182 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427183 {A : Type'} : (term1097 A) = (term1116 A).
Proof. exact (MK_COMB (@lem5427182 A) (@lem5427181 A)). Qed.
Lemma lem5427184 {A : Type'} : ((term1096 A) = (term1097 A)) = ((term1093 A) = (term1116 A)).
Proof. exact (MK_COMB (@lem5427172 A) (@lem5427183 A)). Qed.
Lemma lem5427185 {A : Type'} : (term1093 A) = (term1116 A).
Proof. exact (EQ_MP (@lem5427184 A) (@lem5427159 A)). Qed.
Lemma lem5427187 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427188 {A : Type'} (P : type172 A) : (term1094 A P) = (term1095 A P).
Proof. exact (@lem5427187 (type686 A) (type954 A) P). Qed.
Lemma lem5427189 {A : Type'} (i : type177 A) : (term1117 A i) = (term1118 A i).
Proof. exact (@lem5427188 A (term1119 A i)). Qed.
Lemma lem5427190 {A : Type'} (i : type177 A) (s : type686 A) : (term1120 A i s) = (term1121 A i s).
Proof. exact (eq_refl (term1120 A i s)). Qed.
Lemma lem5427191 {A : Type'} (j : type954 A) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5427192 {A : Type'} (i : type177 A) (s : type686 A) (j : type954 A) : (term1122 A i s j) = (term1123 A i s j).
Proof. exact (MK_COMB (@lem5427190 A i s) (@lem5427191 A j)). Qed.
Lemma lem5427193 {A : Type'} (i : type177 A) (j : type954 A) (s : type686 A) : (term1123 A i s j) = (term1124 A i j s).
Proof. exact (eq_refl (term1123 A i s j)). Qed.
Lemma lem5427194 {A : Type'} (i : type177 A) (j : type954 A) (s : type686 A) : (term1122 A i s j) = (term1124 A i j s).
Proof. exact (TRANS (@lem5427192 A i s j) (@lem5427193 A i j s)). Qed.
Lemma lem5427195 {A : Type'} (i : type177 A) (s : type686 A) : (term1125 A i s) = (term1121 A i s).
Proof. exact (fun_ext (fun j : type954 A => @lem5427194 A i j s)). Qed.
Lemma lem5427196 {A : Type'} : (@ex ((nat -> A -> Prop) -> nat)) = (@ex ((nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427197 {A : Type'} (i : type177 A) (s : type686 A) : (term1126 A i s) = (term1109 A i s).
Proof. exact (MK_COMB (@lem5427196 A) (@lem5427195 A i s)). Qed.
Lemma lem5427198 {A : Type'} (i : type177 A) : (term1127 A i) = (term1111 A i).
Proof. exact (fun_ext (fun s : type686 A => @lem5427197 A i s)). Qed.
Lemma lem5427199 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427200 {A : Type'} (i : type177 A) : (term1117 A i) = (term1113 A i).
Proof. exact (MK_COMB (@lem5427199 A) (@lem5427198 A i)). Qed.
Lemma lem5427201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427202 {A : Type'} (i : type177 A) : (term1128 A i) = (term1129 A i).
Proof. exact (MK_COMB (@lem5427201) (@lem5427200 A i)). Qed.
Lemma lem5427203 {A : Type'} (i : type177 A) (s : type686 A) : (term1120 A i s) = (term1121 A i s).
Proof. exact (eq_refl (term1120 A i s)). Qed.
Lemma lem5427204 {A : Type'} (j : type177 A) (s : type686 A) : (j s) = (j s).
Proof. exact (eq_refl (j s)). Qed.
Lemma lem5427205 {A : Type'} (i : type177 A) (j : type177 A) (s : type686 A) : (term1130 A i j s) = (term1131 A i j s).
Proof. exact (MK_COMB (@lem5427203 A i s) (@lem5427204 A j s)). Qed.
Lemma lem5427206 {A : Type'} (i : type177 A) (j : type177 A) (s : type686 A) : (term1131 A i j s) = (term1132 A i j s).
Proof. exact (eq_refl (term1131 A i j s)). Qed.
Lemma lem5427207 {A : Type'} (i : type177 A) (j : type177 A) (s : type686 A) : (term1130 A i j s) = (term1132 A i j s).
Proof. exact (TRANS (@lem5427205 A i j s) (@lem5427206 A i j s)). Qed.
Lemma lem5427208 {A : Type'} (i : type177 A) (j : type177 A) : (term1133 A i j) = (term1134 A i j).
Proof. exact (fun_ext (fun s : type686 A => @lem5427207 A i j s)). Qed.
Lemma lem5427209 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427210 {A : Type'} (i : type177 A) (j : type177 A) : (term1135 A i j) = (term1136 A i j).
Proof. exact (MK_COMB (@lem5427209 A) (@lem5427208 A i j)). Qed.
Lemma lem5427211 {A : Type'} (i : type177 A) : (term1137 A i) = (term1138 A i).
Proof. exact (fun_ext (fun j : type177 A => @lem5427210 A i j)). Qed.
Lemma lem5427212 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427213 {A : Type'} (i : type177 A) : (term1118 A i) = (term1139 A i).
Proof. exact (MK_COMB (@lem5427212 A) (@lem5427211 A i)). Qed.
Lemma lem5427214 {A : Type'} (i : type177 A) : ((term1117 A i) = (term1118 A i)) = ((term1113 A i) = (term1139 A i)).
Proof. exact (MK_COMB (@lem5427202 A i) (@lem5427213 A i)). Qed.
Lemma lem5427215 {A : Type'} (i : type177 A) : (term1113 A i) = (term1139 A i).
Proof. exact (EQ_MP (@lem5427214 A i) (@lem5427189 A i)). Qed.
Lemma lem5427216 {A : Type'} : (term1115 A) = (term1140 A).
Proof. exact (fun_ext (fun i : type177 A => @lem5427215 A i)). Qed.
Lemma lem5427217 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427218 {A : Type'} : (term1116 A) = (term1141 A).
Proof. exact (MK_COMB (@lem5427217 A) (@lem5427216 A)). Qed.
Lemma lem5427219 {A : Type'} : (term1093 A) = (term1141 A).
Proof. exact (TRANS (@lem5427185 A) (@lem5427218 A)). Qed.
Lemma lem5427220 {A : Type'} : (term974 A) = (term1141 A).
Proof. exact (TRANS (@lem5427155 A) (@lem5427219 A)). Qed.
Lemma lem5427221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427222 {A : Type'} : (term976 A) = (term1142 A).
Proof. exact (MK_COMB (@lem5427221) (@lem5427220 A)). Qed.
Lemma lem5427224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427225 {A : Type'} (P : Prop) (Q : type953 A) : (term1143 A P Q) = (term1144 A P Q).
Proof. exact (@lem5427224 (type1597 A) P Q). Qed.
Lemma lem5427226 {A : Type'} (s : type686 A) : (term1145 A s) = (term1146 A s).
Proof. exact (@lem5427225 A (term1147 A s) (term945 A s)). Qed.
Lemma lem5427227 {A : Type'} (f : type1597 A) (s : type686 A) : (term1148 A s f) = (term935 A f s).
Proof. exact (eq_refl (term1148 A s f)). Qed.
Lemma lem5427228 {A : Type'} (s : type686 A) : (term1149 A s) = (term945 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427227 A f s)). Qed.
Lemma lem5427229 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem5427230 {A : Type'} (s : type686 A) : (term1150 A s) = (term946 A s).
Proof. exact (MK_COMB (@lem5427229 A) (@lem5427228 A s)). Qed.
Lemma lem5427231 {A : Type'} (s : type686 A) : (term947 A s) = (term947 A s).
Proof. exact (eq_refl (term947 A s)). Qed.
Lemma lem5427232 {A : Type'} (s : type686 A) : (term1145 A s) = (term949 A s).
Proof. exact (MK_COMB (@lem5427231 A s) (@lem5427230 A s)). Qed.
Lemma lem5427233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427234 {A : Type'} (s : type686 A) : (term1151 A s) = (term1152 A s).
Proof. exact (MK_COMB (@lem5427233) (@lem5427232 A s)). Qed.
Lemma lem5427235 {A : Type'} (f : type1597 A) (s : type686 A) : (term1148 A s f) = (term935 A f s).
Proof. exact (eq_refl (term1148 A s f)). Qed.
Lemma lem5427236 {A : Type'} (s : type686 A) : (term947 A s) = (term947 A s).
Proof. exact (eq_refl (term947 A s)). Qed.
Lemma lem5427237 {A : Type'} (f : type1597 A) (s : type686 A) : (term1153 A s f) = (term1154 A f s).
Proof. exact (MK_COMB (@lem5427236 A s) (@lem5427235 A f s)). Qed.
Lemma lem5427238 {A : Type'} (s : type686 A) : (term1155 A s) = (term1156 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427237 A f s)). Qed.
Lemma lem5427239 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem5427240 {A : Type'} (s : type686 A) : (term1146 A s) = (term1157 A s).
Proof. exact (MK_COMB (@lem5427239 A) (@lem5427238 A s)). Qed.
Lemma lem5427241 {A : Type'} (s : type686 A) : ((term1145 A s) = (term1146 A s)) = ((term949 A s) = (term1157 A s)).
Proof. exact (MK_COMB (@lem5427234 A s) (@lem5427240 A s)). Qed.
Lemma lem5427242 {A : Type'} (s : type686 A) : (term949 A s) = (term1157 A s).
Proof. exact (EQ_MP (@lem5427241 A s) (@lem5427226 A s)). Qed.
Lemma lem5427243 {A : Type'} : (term964 A) = (term1158 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5427242 A s)). Qed.
Lemma lem5427244 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427245 {A : Type'} : (term979 A) = (term1159 A).
Proof. exact (MK_COMB (@lem5427244 A) (@lem5427243 A)). Qed.
Lemma lem5427247 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427248 {A : Type'} (P : type176 A) : (term1160 A P) = (term1161 A P).
Proof. exact (@lem5427247 (type686 A) (type1597 A) P). Qed.
Lemma lem5427249 {A : Type'} : (term1162 A) = (term1163 A).
Proof. exact (@lem5427248 A (term1164 A)). Qed.
Lemma lem5427250 {A : Type'} (s : type686 A) : (term1165 A s) = (term1156 A s).
Proof. exact (eq_refl (term1165 A s)). Qed.
Lemma lem5427251 {A : Type'} (f : type1597 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5427252 {A : Type'} (s : type686 A) (f : type1597 A) : (term1166 A s f) = (term1167 A s f).
Proof. exact (MK_COMB (@lem5427250 A s) (@lem5427251 A f)). Qed.
Lemma lem5427253 {A : Type'} (f : type1597 A) (s : type686 A) : (term1167 A s f) = (term1154 A f s).
Proof. exact (eq_refl (term1167 A s f)). Qed.
Lemma lem5427254 {A : Type'} (f : type1597 A) (s : type686 A) : (term1166 A s f) = (term1154 A f s).
Proof. exact (TRANS (@lem5427252 A s f) (@lem5427253 A f s)). Qed.
Lemma lem5427255 {A : Type'} (s : type686 A) : (term1168 A s) = (term1156 A s).
Proof. exact (fun_ext (fun f : type1597 A => @lem5427254 A f s)). Qed.
Lemma lem5427256 {A : Type'} : (@ex (nat -> A -> Prop)) = (@ex (nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> A -> Prop))). Qed.
Lemma lem5427257 {A : Type'} (s : type686 A) : (term1169 A s) = (term1157 A s).
Proof. exact (MK_COMB (@lem5427256 A) (@lem5427255 A s)). Qed.
Lemma lem5427258 {A : Type'} : (term1170 A) = (term1158 A).
Proof. exact (fun_ext (fun s : type686 A => @lem5427257 A s)). Qed.
Lemma lem5427259 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427260 {A : Type'} : (term1162 A) = (term1159 A).
Proof. exact (MK_COMB (@lem5427259 A) (@lem5427258 A)). Qed.
Lemma lem5427261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427262 {A : Type'} : (term1171 A) = (term1172 A).
Proof. exact (MK_COMB (@lem5427261) (@lem5427260 A)). Qed.
Lemma lem5427263 {A : Type'} (s : type686 A) : (term1165 A s) = (term1156 A s).
Proof. exact (eq_refl (term1165 A s)). Qed.
Lemma lem5427264 {A : Type'} (f : type179 A) (s : type686 A) : (f s) = (f s).
Proof. exact (eq_refl (f s)). Qed.
Lemma lem5427265 {A : Type'} (f : type179 A) (s : type686 A) : (term1173 A f s) = (term1174 A f s).
Proof. exact (MK_COMB (@lem5427263 A s) (@lem5427264 A f s)). Qed.
Lemma lem5427266 {A : Type'} (f : type179 A) (s : type686 A) : (term1174 A f s) = (term1175 A f s).
Proof. exact (eq_refl (term1174 A f s)). Qed.
Lemma lem5427267 {A : Type'} (f : type179 A) (s : type686 A) : (term1173 A f s) = (term1175 A f s).
Proof. exact (TRANS (@lem5427265 A f s) (@lem5427266 A f s)). Qed.
Lemma lem5427268 {A : Type'} (f : type179 A) : (term1176 A f) = (term1177 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem5427267 A f s)). Qed.
Lemma lem5427269 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem5427270 {A : Type'} (f : type179 A) : (term1178 A f) = (term1179 A f).
Proof. exact (MK_COMB (@lem5427269 A) (@lem5427268 A f)). Qed.
Lemma lem5427271 {A : Type'} : (term1180 A) = (term1181 A).
Proof. exact (fun_ext (fun f : type179 A => @lem5427270 A f)). Qed.
Lemma lem5427272 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)) = (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop))). Qed.
Lemma lem5427273 {A : Type'} : (term1163 A) = (term1182 A).
Proof. exact (MK_COMB (@lem5427272 A) (@lem5427271 A)). Qed.
Lemma lem5427274 {A : Type'} : ((term1162 A) = (term1163 A)) = ((term1159 A) = (term1182 A)).
Proof. exact (MK_COMB (@lem5427262 A) (@lem5427273 A)). Qed.
Lemma lem5427275 {A : Type'} : (term1159 A) = (term1182 A).
Proof. exact (EQ_MP (@lem5427274 A) (@lem5427249 A)). Qed.
Lemma lem5427276 {A : Type'} : (term979 A) = (term1182 A).
Proof. exact (TRANS (@lem5427245 A) (@lem5427275 A)). Qed.
Lemma lem5427277 {A : Type'} : (term980 A) = (term1183 A).
Proof. exact (MK_COMB (@lem5427222 A) (@lem5427276 A)). Qed.
Lemma lem5427279 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5427280 {A : Type'} (P : type71 A) (Q : Prop) : (term1184 A P Q) = (term1185 A P Q).
Proof. exact (@lem5427279 (type177 A) P Q). Qed.
Lemma lem5427281 {A : Type'} : (term1186 A) = (term1187 A).
Proof. exact (@lem5427280 A (term1140 A) (term1182 A)). Qed.
Lemma lem5427282 {A : Type'} (i : type177 A) : (term1188 A i) = (term1139 A i).
Proof. exact (eq_refl (term1188 A i)). Qed.
Lemma lem5427283 {A : Type'} : (term1189 A) = (term1140 A).
Proof. exact (fun_ext (fun i : type177 A => @lem5427282 A i)). Qed.
Lemma lem5427284 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427285 {A : Type'} : (term1190 A) = (term1141 A).
Proof. exact (MK_COMB (@lem5427284 A) (@lem5427283 A)). Qed.
Lemma lem5427286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427287 {A : Type'} : (term1191 A) = (term1142 A).
Proof. exact (MK_COMB (@lem5427286) (@lem5427285 A)). Qed.
Lemma lem5427288 {A : Type'} : (term1182 A) = (term1182 A).
Proof. exact (eq_refl (term1182 A)). Qed.
Lemma lem5427289 {A : Type'} : (term1186 A) = (term1183 A).
Proof. exact (MK_COMB (@lem5427287 A) (@lem5427288 A)). Qed.
Lemma lem5427290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427291 {A : Type'} : (term1192 A) = (term1193 A).
Proof. exact (MK_COMB (@lem5427290) (@lem5427289 A)). Qed.
Lemma lem5427292 {A : Type'} (i : type177 A) : (term1188 A i) = (term1139 A i).
Proof. exact (eq_refl (term1188 A i)). Qed.
Lemma lem5427293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427294 {A : Type'} (i : type177 A) : (term1194 A i) = (term1195 A i).
Proof. exact (MK_COMB (@lem5427293) (@lem5427292 A i)). Qed.
Lemma lem5427295 {A : Type'} : (term1182 A) = (term1182 A).
Proof. exact (eq_refl (term1182 A)). Qed.
Lemma lem5427296 {A : Type'} (i : type177 A) : (term1196 A i) = (term1197 A i).
Proof. exact (MK_COMB (@lem5427294 A i) (@lem5427295 A)). Qed.
Lemma lem5427297 {A : Type'} : (term1198 A) = (term1199 A).
Proof. exact (fun_ext (fun i : type177 A => @lem5427296 A i)). Qed.
Lemma lem5427298 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427299 {A : Type'} : (term1187 A) = (term1200 A).
Proof. exact (MK_COMB (@lem5427298 A) (@lem5427297 A)). Qed.
Lemma lem5427300 {A : Type'} : ((term1186 A) = (term1187 A)) = ((term1183 A) = (term1200 A)).
Proof. exact (MK_COMB (@lem5427291 A) (@lem5427299 A)). Qed.
Lemma lem5427301 {A : Type'} : (term1183 A) = (term1200 A).
Proof. exact (EQ_MP (@lem5427300 A) (@lem5427281 A)). Qed.
Lemma lem5427303 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5427304 {A : Type'} (P : type71 A) (Q : Prop) : (term1184 A P Q) = (term1185 A P Q).
Proof. exact (@lem5427303 (type177 A) P Q). Qed.
Lemma lem5427305 {A : Type'} (i : type177 A) : (term1201 A i) = (term1202 A i).
Proof. exact (@lem5427304 A (term1138 A i) (term1182 A)). Qed.
Lemma lem5427306 {A : Type'} (i : type177 A) (j : type177 A) : (term1203 A i j) = (term1136 A i j).
Proof. exact (eq_refl (term1203 A i j)). Qed.
Lemma lem5427307 {A : Type'} (i : type177 A) : (term1204 A i) = (term1138 A i).
Proof. exact (fun_ext (fun j : type177 A => @lem5427306 A i j)). Qed.
Lemma lem5427308 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427309 {A : Type'} (i : type177 A) : (term1205 A i) = (term1139 A i).
Proof. exact (MK_COMB (@lem5427308 A) (@lem5427307 A i)). Qed.
Lemma lem5427310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427311 {A : Type'} (i : type177 A) : (term1206 A i) = (term1195 A i).
Proof. exact (MK_COMB (@lem5427310) (@lem5427309 A i)). Qed.
Lemma lem5427312 {A : Type'} : (term1182 A) = (term1182 A).
Proof. exact (eq_refl (term1182 A)). Qed.
Lemma lem5427313 {A : Type'} (i : type177 A) : (term1201 A i) = (term1197 A i).
Proof. exact (MK_COMB (@lem5427311 A i) (@lem5427312 A)). Qed.
Lemma lem5427314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427315 {A : Type'} (i : type177 A) : (term1207 A i) = (term1208 A i).
Proof. exact (MK_COMB (@lem5427314) (@lem5427313 A i)). Qed.
Lemma lem5427316 {A : Type'} (i : type177 A) (j : type177 A) : (term1203 A i j) = (term1136 A i j).
Proof. exact (eq_refl (term1203 A i j)). Qed.
Lemma lem5427317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427318 {A : Type'} (i : type177 A) (j : type177 A) : (term1209 A i j) = (term1210 A i j).
Proof. exact (MK_COMB (@lem5427317) (@lem5427316 A i j)). Qed.
Lemma lem5427319 {A : Type'} : (term1182 A) = (term1182 A).
Proof. exact (eq_refl (term1182 A)). Qed.
Lemma lem5427320 {A : Type'} (i : type177 A) (j : type177 A) : (term1211 A i j) = (term1212 A i j).
Proof. exact (MK_COMB (@lem5427318 A i j) (@lem5427319 A)). Qed.
Lemma lem5427321 {A : Type'} (i : type177 A) : (term1213 A i) = (term1214 A i).
Proof. exact (fun_ext (fun j : type177 A => @lem5427320 A i j)). Qed.
Lemma lem5427322 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427323 {A : Type'} (i : type177 A) : (term1202 A i) = (term1215 A i).
Proof. exact (MK_COMB (@lem5427322 A) (@lem5427321 A i)). Qed.
Lemma lem5427324 {A : Type'} (i : type177 A) : ((term1201 A i) = (term1202 A i)) = ((term1197 A i) = (term1215 A i)).
Proof. exact (MK_COMB (@lem5427315 A i) (@lem5427323 A i)). Qed.
Lemma lem5427325 {A : Type'} (i : type177 A) : (term1197 A i) = (term1215 A i).
Proof. exact (EQ_MP (@lem5427324 A i) (@lem5427305 A i)). Qed.
Lemma lem5427327 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5427328 {A : Type'} (P : Prop) (Q : type73 A) : (term1216 A P Q) = (term1217 A P Q).
Proof. exact (@lem5427327 (type179 A) P Q). Qed.
Lemma lem5427329 {A : Type'} (i : type177 A) (j : type177 A) : (term1218 A i j) = (term1219 A i j).
Proof. exact (@lem5427328 A (term1136 A i j) (term1181 A)). Qed.
Lemma lem5427330 {A : Type'} (f : type179 A) : (term1220 A f) = (term1179 A f).
Proof. exact (eq_refl (term1220 A f)). Qed.
Lemma lem5427331 {A : Type'} : (term1221 A) = (term1181 A).
Proof. exact (fun_ext (fun f : type179 A => @lem5427330 A f)). Qed.
Lemma lem5427332 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)) = (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop))). Qed.
Lemma lem5427333 {A : Type'} : (term1222 A) = (term1182 A).
Proof. exact (MK_COMB (@lem5427332 A) (@lem5427331 A)). Qed.
Lemma lem5427334 {A : Type'} (i : type177 A) (j : type177 A) : (term1210 A i j) = (term1210 A i j).
Proof. exact (eq_refl (term1210 A i j)). Qed.
Lemma lem5427335 {A : Type'} (i : type177 A) (j : type177 A) : (term1218 A i j) = (term1212 A i j).
Proof. exact (MK_COMB (@lem5427334 A i j) (@lem5427333 A)). Qed.
Lemma lem5427336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427337 {A : Type'} (i : type177 A) (j : type177 A) : (term1223 A i j) = (term1224 A i j).
Proof. exact (MK_COMB (@lem5427336) (@lem5427335 A i j)). Qed.
Lemma lem5427338 {A : Type'} (f : type179 A) : (term1220 A f) = (term1179 A f).
Proof. exact (eq_refl (term1220 A f)). Qed.
Lemma lem5427339 {A : Type'} (i : type177 A) (j : type177 A) : (term1210 A i j) = (term1210 A i j).
Proof. exact (eq_refl (term1210 A i j)). Qed.
Lemma lem5427340 {A : Type'} (i : type177 A) (j : type177 A) (f : type179 A) : (term1225 A i j f) = (term1226 A i j f).
Proof. exact (MK_COMB (@lem5427339 A i j) (@lem5427338 A f)). Qed.
Lemma lem5427341 {A : Type'} (i : type177 A) (j : type177 A) : (term1227 A i j) = (term1228 A i j).
Proof. exact (fun_ext (fun f : type179 A => @lem5427340 A i j f)). Qed.
Lemma lem5427342 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)) = (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> nat -> A -> Prop))). Qed.
Lemma lem5427343 {A : Type'} (i : type177 A) (j : type177 A) : (term1219 A i j) = (term1229 A i j).
Proof. exact (MK_COMB (@lem5427342 A) (@lem5427341 A i j)). Qed.
Lemma lem5427344 {A : Type'} (i : type177 A) (j : type177 A) : ((term1218 A i j) = (term1219 A i j)) = ((term1212 A i j) = (term1229 A i j)).
Proof. exact (MK_COMB (@lem5427337 A i j) (@lem5427343 A i j)). Qed.
Lemma lem5427345 {A : Type'} (i : type177 A) (j : type177 A) : (term1212 A i j) = (term1229 A i j).
Proof. exact (EQ_MP (@lem5427344 A i j) (@lem5427329 A i j)). Qed.
Lemma lem5427346 {A : Type'} (i : type177 A) : (term1214 A i) = (term1230 A i).
Proof. exact (fun_ext (fun j : type177 A => @lem5427345 A i j)). Qed.
Lemma lem5427347 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427348 {A : Type'} (i : type177 A) : (term1215 A i) = (term1231 A i).
Proof. exact (MK_COMB (@lem5427347 A) (@lem5427346 A i)). Qed.
Lemma lem5427349 {A : Type'} (i : type177 A) : (term1197 A i) = (term1231 A i).
Proof. exact (TRANS (@lem5427325 A i) (@lem5427348 A i)). Qed.
Lemma lem5427350 {A : Type'} : (term1199 A) = (term1232 A).
Proof. exact (fun_ext (fun i : type177 A => @lem5427349 A i)). Qed.
Lemma lem5427351 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)) = (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> (nat -> A -> Prop) -> nat))). Qed.
Lemma lem5427352 {A : Type'} : (term1200 A) = (term1233 A).
Proof. exact (MK_COMB (@lem5427351 A) (@lem5427350 A)). Qed.
Lemma lem5427353 {A : Type'} : (term1183 A) = (term1233 A).
Proof. exact (TRANS (@lem5427301 A) (@lem5427352 A)). Qed.
Lemma lem5427354 {A : Type'} : (term980 A) = (term1233 A).
Proof. exact (TRANS (@lem5427277 A) (@lem5427353 A)). Qed.
Lemma lem5427355 {A : Type'} : (term958 A) = (term1233 A).
Proof. exact (TRANS (@lem5426709 A) (@lem5427354 A)). Qed.
Lemma lem5427356 {A : Type'} : (term13 A) = (term1233 A).
Proof. exact (TRANS (@lem5426682 A) (@lem5427355 A)). Qed.
Lemma lem5427357 {A : Type'} (h1 : term13 A) : term1233 A.
Proof. exact (EQ_MP (@lem5427356 A) (@lem5424291 A h1)). Qed.
Lemma lem5427370 (s : nat -> Prop) (i : nat) (f : nat -> nat) (j : nat) : (term1234 s i f j) = (term1235 s i f j).
Proof. exact (@lem17045 (term1236 j s) ((f i) = (f j))). Qed.
Lemma lem5427375 (i : nat) (s : nat -> Prop) : (term1237 i s) = (term1237 i s).
Proof. exact (eq_refl (term1237 i s)). Qed.
Lemma lem5427376 (s : nat -> Prop) (i : nat) (f : nat -> nat) (j : nat) : (term1238 s i f j) = (term1239 s i f j).
Proof. exact (MK_COMB (@lem5427375 i s) (@lem5427370 s i f j)). Qed.
Lemma lem5427377 (s : nat -> Prop) (i : nat) (f : nat -> nat) (j : nat) : (term1240 s i f j) = (term1238 s i f j).
Proof. exact (@lem17045 (term1236 i s) (term1241 s i f j)). Qed.
Lemma lem5427378 (s : nat -> Prop) (i : nat) (f : nat -> nat) (j : nat) : (term1240 s i f j) = (term1239 s i f j).
Proof. exact (TRANS (@lem5427377 s i f j) (@lem5427376 s i f j)). Qed.
Lemma lem5427383 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5427388 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1242 s f i j) = (term1243 s f i j).
Proof. exact (@lem17362 (term1244 s i f j) (i = j)). Qed.
Lemma lem5427389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427390 (s : nat -> Prop) (i : nat) (f : nat -> nat) (j : nat) : (term1245 s i f j) = (term1246 s i f j).
Proof. exact (MK_COMB (@lem5427389) (@lem5427378 s i f j)). Qed.
Lemma lem5427391 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1247 s f i j) = (term1248 s f i j).
Proof. exact (MK_COMB (@lem5427390 s i f j) (@lem5427383 i j)). Qed.
Lemma lem5427392 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term66 s f i j) = (term1247 s f i j).
Proof. exact (@lem17265 (term1244 s i f j) (i = j)). Qed.
Lemma lem5427393 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term66 s f i j) = (term1248 s f i j).
Proof. exact (TRANS (@lem5427392 s f i j) (@lem5427391 s f i j)). Qed.
Lemma lem5427394 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5427395 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1249 s f i) = (term1250 s f i).
Proof. exact (@lem5427394 (term67 s f i)). Qed.
Lemma lem5427396 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1251 s f i j) = (term66 s f i j).
Proof. exact (eq_refl (term1251 s f i j)). Qed.
Lemma lem5427397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5427398 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1252 s f i j) = (term1242 s f i j).
Proof. exact (MK_COMB (@lem5427397) (@lem5427396 s f i j)). Qed.
Lemma lem5427399 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1252 s f i j) = (term1243 s f i j).
Proof. exact (TRANS (@lem5427398 s f i j) (@lem5427388 s f i j)). Qed.
Lemma lem5427400 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1253 s f i) = (term1254 s f i).
Proof. exact (fun_ext (fun j : nat => @lem5427399 s f i j)). Qed.
Lemma lem5427401 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427402 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1250 s f i) = (term1255 s f i).
Proof. exact (MK_COMB (@lem5427401) (@lem5427400 s f i)). Qed.
Lemma lem5427403 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1249 s f i) = (term1255 s f i).
Proof. exact (TRANS (@lem5427395 s f i) (@lem5427402 s f i)). Qed.
Lemma lem5427404 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term67 s f i) = (term1256 s f i).
Proof. exact (fun_ext (fun j : nat => @lem5427393 s f i j)). Qed.
Lemma lem5427405 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5427406 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term68 s f i) = (term1257 s f i).
Proof. exact (MK_COMB (@lem5427405) (@lem5427404 s f i)). Qed.
Lemma lem5427407 (P : nat -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5427408 (s : nat -> Prop) (f : nat -> nat) : (term1258 s f) = (term1259 s f).
Proof. exact (@lem5427407 (term69 s f)). Qed.
Lemma lem5427409 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1260 s f i) = (term68 s f i).
Proof. exact (eq_refl (term1260 s f i)). Qed.
Lemma lem5427410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5427411 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1261 s f i) = (term1249 s f i).
Proof. exact (MK_COMB (@lem5427410) (@lem5427409 s f i)). Qed.
Lemma lem5427412 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1261 s f i) = (term1255 s f i).
Proof. exact (TRANS (@lem5427411 s f i) (@lem5427403 s f i)). Qed.
Lemma lem5427413 (s : nat -> Prop) (f : nat -> nat) : (term1262 s f) = (term1263 s f).
Proof. exact (fun_ext (fun i : nat => @lem5427412 s f i)). Qed.
Lemma lem5427414 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427415 (s : nat -> Prop) (f : nat -> nat) : (term1259 s f) = (term1264 s f).
Proof. exact (MK_COMB (@lem5427414) (@lem5427413 s f)). Qed.
Lemma lem5427416 (s : nat -> Prop) (f : nat -> nat) : (term1258 s f) = (term1264 s f).
Proof. exact (TRANS (@lem5427408 s f) (@lem5427415 s f)). Qed.
Lemma lem5427417 (s : nat -> Prop) (f : nat -> nat) : (term69 s f) = (term1265 s f).
Proof. exact (fun_ext (fun i : nat => @lem5427406 s f i)). Qed.
Lemma lem5427418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5427419 (s : nat -> Prop) (f : nat -> nat) : (term70 s f) = (term1266 s f).
Proof. exact (MK_COMB (@lem5427418) (@lem5427417 s f)). Qed.
Lemma lem5427420 (f : nat -> nat) (s : nat -> Prop) : (term1267 f s) = (term1267 f s).
Proof. exact (eq_refl (term1267 f s)). Qed.
Lemma lem5427421 (f : nat -> nat) (s : nat -> Prop) : (s = (term65 f s)) = (s = (term65 f s)).
Proof. exact (eq_refl (s = (term65 f s))). Qed.
Lemma lem5427422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427423 (s : nat -> Prop) (f : nat -> nat) : (term1268 s f) = (term1269 s f).
Proof. exact (MK_COMB (@lem5427422) (@lem5427416 s f)). Qed.
Lemma lem5427424 (f : nat -> nat) (s : nat -> Prop) : (term1270 f s) = (term1271 f s).
Proof. exact (MK_COMB (@lem5427423 s f) (@lem5427420 f s)). Qed.
Lemma lem5427425 (f : nat -> nat) (s : nat -> Prop) : (term1272 f s) = (term1270 f s).
Proof. exact (@lem17045 (term70 s f) (s = (term65 f s))). Qed.
Lemma lem5427426 (f : nat -> nat) (s : nat -> Prop) : (term1272 f s) = (term1271 f s).
Proof. exact (TRANS (@lem5427425 f s) (@lem5427424 f s)). Qed.
Lemma lem5427427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427428 (s : nat -> Prop) (f : nat -> nat) : (term71 s f) = (term1273 s f).
Proof. exact (MK_COMB (@lem5427427) (@lem5427419 s f)). Qed.
Lemma lem5427429 (f : nat -> nat) (s : nat -> Prop) : (term72 f s) = (term1274 f s).
Proof. exact (MK_COMB (@lem5427428 s f) (@lem5427421 f s)). Qed.
Lemma lem5427430 (P : type1002) : (term1275 P) = (term1276 P).
Proof. exact (@lem18394 (nat -> nat) P). Qed.
Lemma lem5427431 (s : nat -> Prop) : (term1277 s) = (term1278 s).
Proof. exact (@lem5427430 (term73 s)). Qed.
Lemma lem5427432 (f : nat -> nat) (s : nat -> Prop) : (term1279 s f) = (term72 f s).
Proof. exact (eq_refl (term1279 s f)). Qed.
Lemma lem5427433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5427434 (f : nat -> nat) (s : nat -> Prop) : (term1280 s f) = (term1272 f s).
Proof. exact (MK_COMB (@lem5427433) (@lem5427432 f s)). Qed.
Lemma lem5427435 (f : nat -> nat) (s : nat -> Prop) : (term1280 s f) = (term1271 f s).
Proof. exact (TRANS (@lem5427434 f s) (@lem5427426 f s)). Qed.
Lemma lem5427436 (s : nat -> Prop) : (term1281 s) = (term1282 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427435 f s)). Qed.
Lemma lem5427437 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427438 (s : nat -> Prop) : (term1278 s) = (term1283 s).
Proof. exact (MK_COMB (@lem5427437) (@lem5427436 s)). Qed.
Lemma lem5427439 (s : nat -> Prop) : (term1277 s) = (term1283 s).
Proof. exact (TRANS (@lem5427431 s) (@lem5427438 s)). Qed.
Lemma lem5427440 (s : nat -> Prop) : (term73 s) = (term1284 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427429 f s)). Qed.
Lemma lem5427441 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5427442 (s : nat -> Prop) : (term74 s) = (term1285 s).
Proof. exact (MK_COMB (@lem5427441) (@lem5427440 s)). Qed.
Lemma lem5427444 (s : nat -> Prop) : (term1286 s) = (term1286 s).
Proof. exact (eq_refl (term1286 s)). Qed.
Lemma lem5427445 (s : nat -> Prop) : (term1287 s) = (term1288 s).
Proof. exact (MK_COMB (@lem5427444 s) (@lem5427442 s)). Qed.
Lemma lem5427447 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427448 (s : nat -> Prop) : (term1290 s) = (term1291 s).
Proof. exact (MK_COMB (@lem5427447 s) (@lem5427439 s)). Qed.
Lemma lem5427449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427450 (s : nat -> Prop) : (term1292 s) = (term1293 s).
Proof. exact (MK_COMB (@lem5427449) (@lem5427448 s)). Qed.
Lemma lem5427451 (s : nat -> Prop) : (term1294 s) = (term1295 s).
Proof. exact (MK_COMB (@lem5427450 s) (@lem5427445 s)). Qed.
Lemma lem5427452 (s : nat -> Prop) : ((@FINITE nat s) = (term74 s)) = (term1294 s).
Proof. exact (@lem17784 (@FINITE nat s) (term74 s)). Qed.
Lemma lem5427453 (s : nat -> Prop) : ((@FINITE nat s) = (term74 s)) = (term1295 s).
Proof. exact (TRANS (@lem5427452 s) (@lem5427451 s)). Qed.
Lemma lem5427454 : term76 = term1296.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427453 s)). Qed.
Lemma lem5427455 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427456 : term12 = term1297.
Proof. exact (MK_COMB (@lem5427455) (@lem5427454)). Qed.
Lemma lem5427458 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5427459 (P : type993) (Q : type993) : (term1298 P Q) = (term1299 P Q).
Proof. exact (@lem5427458 (nat -> Prop) P Q). Qed.
Lemma lem5427460 : term1300 = term1301.
Proof. exact (@lem5427459 term1302 term1303). Qed.
Lemma lem5427461 (s : nat -> Prop) : (term1304 s) = (term1291 s).
Proof. exact (eq_refl (term1304 s)). Qed.
Lemma lem5427462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427463 (s : nat -> Prop) : (term1305 s) = (term1293 s).
Proof. exact (MK_COMB (@lem5427462) (@lem5427461 s)). Qed.
Lemma lem5427464 (s : nat -> Prop) : (term1306 s) = (term1288 s).
Proof. exact (eq_refl (term1306 s)). Qed.
Lemma lem5427465 (s : nat -> Prop) : (term1307 s) = (term1295 s).
Proof. exact (MK_COMB (@lem5427463 s) (@lem5427464 s)). Qed.
Lemma lem5427466 : term1308 = term1296.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427465 s)). Qed.
Lemma lem5427467 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427468 : term1300 = term1297.
Proof. exact (MK_COMB (@lem5427467) (@lem5427466)). Qed.
Lemma lem5427469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427470 : term1309 = term1310.
Proof. exact (MK_COMB (@lem5427469) (@lem5427468)). Qed.
Lemma lem5427471 (s : nat -> Prop) : (term1304 s) = (term1291 s).
Proof. exact (eq_refl (term1304 s)). Qed.
Lemma lem5427472 : term1311 = term1302.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427471 s)). Qed.
Lemma lem5427473 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427474 : term1312 = term1313.
Proof. exact (MK_COMB (@lem5427473) (@lem5427472)). Qed.
Lemma lem5427475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427476 : term1314 = term1315.
Proof. exact (MK_COMB (@lem5427475) (@lem5427474)). Qed.
Lemma lem5427477 (s : nat -> Prop) : (term1306 s) = (term1288 s).
Proof. exact (eq_refl (term1306 s)). Qed.
Lemma lem5427478 : term1316 = term1303.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427477 s)). Qed.
Lemma lem5427479 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427480 : term1317 = term1318.
Proof. exact (MK_COMB (@lem5427479) (@lem5427478)). Qed.
Lemma lem5427481 : term1301 = term1319.
Proof. exact (MK_COMB (@lem5427476) (@lem5427480)). Qed.
Lemma lem5427482 : (term1300 = term1301) = (term1297 = term1319).
Proof. exact (MK_COMB (@lem5427470) (@lem5427481)). Qed.
Lemma lem5427483 : term1297 = term1319.
Proof. exact (EQ_MP (@lem5427482) (@lem5427460)). Qed.
Lemma lem5427761 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5427762 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5427761 nat P Q). Qed.
Lemma lem5427763 (f : nat -> nat) (s : nat -> Prop) : (term1320 f s) = (term1321 f s).
Proof. exact (@lem5427762 (term1263 s f) (term1267 f s)). Qed.
Lemma lem5427764 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1322 s f i) = (term1255 s f i).
Proof. exact (eq_refl (term1322 s f i)). Qed.
Lemma lem5427765 (s : nat -> Prop) (f : nat -> nat) : (term1323 s f) = (term1263 s f).
Proof. exact (fun_ext (fun i : nat => @lem5427764 s f i)). Qed.
Lemma lem5427766 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427767 (s : nat -> Prop) (f : nat -> nat) : (term1324 s f) = (term1264 s f).
Proof. exact (MK_COMB (@lem5427766) (@lem5427765 s f)). Qed.
Lemma lem5427768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427769 (s : nat -> Prop) (f : nat -> nat) : (term1325 s f) = (term1269 s f).
Proof. exact (MK_COMB (@lem5427768) (@lem5427767 s f)). Qed.
Lemma lem5427770 (f : nat -> nat) (s : nat -> Prop) : (term1267 f s) = (term1267 f s).
Proof. exact (eq_refl (term1267 f s)). Qed.
Lemma lem5427771 (f : nat -> nat) (s : nat -> Prop) : (term1320 f s) = (term1271 f s).
Proof. exact (MK_COMB (@lem5427769 s f) (@lem5427770 f s)). Qed.
Lemma lem5427772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427773 (f : nat -> nat) (s : nat -> Prop) : (term1326 f s) = (term1327 f s).
Proof. exact (MK_COMB (@lem5427772) (@lem5427771 f s)). Qed.
Lemma lem5427774 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1322 s f i) = (term1255 s f i).
Proof. exact (eq_refl (term1322 s f i)). Qed.
Lemma lem5427775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427776 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1328 s f i) = (term1329 s f i).
Proof. exact (MK_COMB (@lem5427775) (@lem5427774 s f i)). Qed.
Lemma lem5427777 (f : nat -> nat) (s : nat -> Prop) : (term1267 f s) = (term1267 f s).
Proof. exact (eq_refl (term1267 f s)). Qed.
Lemma lem5427778 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1330 i f s) = (term1331 i f s).
Proof. exact (MK_COMB (@lem5427776 s f i) (@lem5427777 f s)). Qed.
Lemma lem5427779 (f : nat -> nat) (s : nat -> Prop) : (term1332 f s) = (term1333 f s).
Proof. exact (fun_ext (fun i : nat => @lem5427778 i f s)). Qed.
Lemma lem5427780 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427781 (f : nat -> nat) (s : nat -> Prop) : (term1321 f s) = (term1334 f s).
Proof. exact (MK_COMB (@lem5427780) (@lem5427779 f s)). Qed.
Lemma lem5427782 (f : nat -> nat) (s : nat -> Prop) : ((term1320 f s) = (term1321 f s)) = ((term1271 f s) = (term1334 f s)).
Proof. exact (MK_COMB (@lem5427773 f s) (@lem5427781 f s)). Qed.
Lemma lem5427783 (f : nat -> nat) (s : nat -> Prop) : (term1271 f s) = (term1334 f s).
Proof. exact (EQ_MP (@lem5427782 f s) (@lem5427763 f s)). Qed.
Lemma lem5427785 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5427786 (P : nat -> Prop) (Q : Prop) : (term261 P Q) = (term262 P Q).
Proof. exact (@lem5427785 nat P Q). Qed.
Lemma lem5427787 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1335 i f s) = (term1336 i f s).
Proof. exact (@lem5427786 (term1254 s f i) (term1267 f s)). Qed.
Lemma lem5427788 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1337 s f i j) = (term1243 s f i j).
Proof. exact (eq_refl (term1337 s f i j)). Qed.
Lemma lem5427789 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1338 s f i) = (term1254 s f i).
Proof. exact (fun_ext (fun j : nat => @lem5427788 s f i j)). Qed.
Lemma lem5427790 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427791 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1339 s f i) = (term1255 s f i).
Proof. exact (MK_COMB (@lem5427790) (@lem5427789 s f i)). Qed.
Lemma lem5427792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427793 (s : nat -> Prop) (f : nat -> nat) (i : nat) : (term1340 s f i) = (term1329 s f i).
Proof. exact (MK_COMB (@lem5427792) (@lem5427791 s f i)). Qed.
Lemma lem5427794 (f : nat -> nat) (s : nat -> Prop) : (term1267 f s) = (term1267 f s).
Proof. exact (eq_refl (term1267 f s)). Qed.
Lemma lem5427795 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1335 i f s) = (term1331 i f s).
Proof. exact (MK_COMB (@lem5427793 s f i) (@lem5427794 f s)). Qed.
Lemma lem5427796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427797 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1341 i f s) = (term1342 i f s).
Proof. exact (MK_COMB (@lem5427796) (@lem5427795 i f s)). Qed.
Lemma lem5427798 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1337 s f i j) = (term1243 s f i j).
Proof. exact (eq_refl (term1337 s f i j)). Qed.
Lemma lem5427799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5427800 (s : nat -> Prop) (f : nat -> nat) (i : nat) (j : nat) : (term1343 s f i j) = (term1344 s f i j).
Proof. exact (MK_COMB (@lem5427799) (@lem5427798 s f i j)). Qed.
Lemma lem5427801 (f : nat -> nat) (s : nat -> Prop) : (term1267 f s) = (term1267 f s).
Proof. exact (eq_refl (term1267 f s)). Qed.
Lemma lem5427802 (i : nat) (j : nat) (f : nat -> nat) (s : nat -> Prop) : (term1345 i j f s) = (term1346 i j f s).
Proof. exact (MK_COMB (@lem5427800 s f i j) (@lem5427801 f s)). Qed.
Lemma lem5427803 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1347 i f s) = (term1348 i f s).
Proof. exact (fun_ext (fun j : nat => @lem5427802 i j f s)). Qed.
Lemma lem5427804 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427805 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1336 i f s) = (term1349 i f s).
Proof. exact (MK_COMB (@lem5427804) (@lem5427803 i f s)). Qed.
Lemma lem5427806 (i : nat) (f : nat -> nat) (s : nat -> Prop) : ((term1335 i f s) = (term1336 i f s)) = ((term1331 i f s) = (term1349 i f s)).
Proof. exact (MK_COMB (@lem5427797 i f s) (@lem5427805 i f s)). Qed.
Lemma lem5427807 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1331 i f s) = (term1349 i f s).
Proof. exact (EQ_MP (@lem5427806 i f s) (@lem5427787 i f s)). Qed.
Lemma lem5427808 (f : nat -> nat) (s : nat -> Prop) : (term1333 f s) = (term1350 f s).
Proof. exact (fun_ext (fun i : nat => @lem5427807 i f s)). Qed.
Lemma lem5427809 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427810 (f : nat -> nat) (s : nat -> Prop) : (term1334 f s) = (term1351 f s).
Proof. exact (MK_COMB (@lem5427809) (@lem5427808 f s)). Qed.
Lemma lem5427811 (f : nat -> nat) (s : nat -> Prop) : (term1271 f s) = (term1351 f s).
Proof. exact (TRANS (@lem5427783 f s) (@lem5427810 f s)). Qed.
Lemma lem5427812 (s : nat -> Prop) : (term1282 s) = (term1352 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427811 f s)). Qed.
Lemma lem5427813 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427814 (s : nat -> Prop) : (term1283 s) = (term1353 s).
Proof. exact (MK_COMB (@lem5427813) (@lem5427812 s)). Qed.
Lemma lem5427816 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427817 (P : type1001) : (term1354 P) = (term1355 P).
Proof. exact (@lem5427816 (nat -> nat) nat P). Qed.
Lemma lem5427818 (s : nat -> Prop) : (term1356 s) = (term1357 s).
Proof. exact (@lem5427817 (term1358 s)). Qed.
Lemma lem5427819 (f : nat -> nat) (s : nat -> Prop) : (term1359 s f) = (term1350 f s).
Proof. exact (eq_refl (term1359 s f)). Qed.
Lemma lem5427820 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5427821 (f : nat -> nat) (s : nat -> Prop) (i : nat) : (term1360 s f i) = (term1361 f s i).
Proof. exact (MK_COMB (@lem5427819 f s) (@lem5427820 i)). Qed.
Lemma lem5427822 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1361 f s i) = (term1349 i f s).
Proof. exact (eq_refl (term1361 f s i)). Qed.
Lemma lem5427823 (i : nat) (f : nat -> nat) (s : nat -> Prop) : (term1360 s f i) = (term1349 i f s).
Proof. exact (TRANS (@lem5427821 f s i) (@lem5427822 i f s)). Qed.
Lemma lem5427824 (f : nat -> nat) (s : nat -> Prop) : (term1362 s f) = (term1350 f s).
Proof. exact (fun_ext (fun i : nat => @lem5427823 i f s)). Qed.
Lemma lem5427825 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427826 (f : nat -> nat) (s : nat -> Prop) : (term1363 s f) = (term1351 f s).
Proof. exact (MK_COMB (@lem5427825) (@lem5427824 f s)). Qed.
Lemma lem5427827 (s : nat -> Prop) : (term1364 s) = (term1352 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427826 f s)). Qed.
Lemma lem5427828 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427829 (s : nat -> Prop) : (term1356 s) = (term1353 s).
Proof. exact (MK_COMB (@lem5427828) (@lem5427827 s)). Qed.
Lemma lem5427830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427831 (s : nat -> Prop) : (term1365 s) = (term1366 s).
Proof. exact (MK_COMB (@lem5427830) (@lem5427829 s)). Qed.
Lemma lem5427832 (f : nat -> nat) (s : nat -> Prop) : (term1359 s f) = (term1350 f s).
Proof. exact (eq_refl (term1359 s f)). Qed.
Lemma lem5427833 (i : type1003) (f : nat -> nat) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem5427834 (s : nat -> Prop) (i : type1003) (f : nat -> nat) : (term1367 s i f) = (term1368 s i f).
Proof. exact (MK_COMB (@lem5427832 f s) (@lem5427833 i f)). Qed.
Lemma lem5427835 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1368 s i f) = (term1369 i f s).
Proof. exact (eq_refl (term1368 s i f)). Qed.
Lemma lem5427836 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1367 s i f) = (term1369 i f s).
Proof. exact (TRANS (@lem5427834 s i f) (@lem5427835 i f s)). Qed.
Lemma lem5427837 (i : type1003) (s : nat -> Prop) : (term1370 s i) = (term1371 i s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427836 i f s)). Qed.
Lemma lem5427838 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427839 (i : type1003) (s : nat -> Prop) : (term1372 s i) = (term1373 i s).
Proof. exact (MK_COMB (@lem5427838) (@lem5427837 i s)). Qed.
Lemma lem5427840 (s : nat -> Prop) : (term1374 s) = (term1375 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427839 i s)). Qed.
Lemma lem5427841 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427842 (s : nat -> Prop) : (term1357 s) = (term1376 s).
Proof. exact (MK_COMB (@lem5427841) (@lem5427840 s)). Qed.
Lemma lem5427843 (s : nat -> Prop) : ((term1356 s) = (term1357 s)) = ((term1353 s) = (term1376 s)).
Proof. exact (MK_COMB (@lem5427831 s) (@lem5427842 s)). Qed.
Lemma lem5427844 (s : nat -> Prop) : (term1353 s) = (term1376 s).
Proof. exact (EQ_MP (@lem5427843 s) (@lem5427818 s)). Qed.
Lemma lem5427846 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427847 (P : type1001) : (term1354 P) = (term1355 P).
Proof. exact (@lem5427846 (nat -> nat) nat P). Qed.
Lemma lem5427848 (i : type1003) (s : nat -> Prop) : (term1377 i s) = (term1378 i s).
Proof. exact (@lem5427847 (term1379 i s)). Qed.
Lemma lem5427849 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1380 i s f) = (term1381 i f s).
Proof. exact (eq_refl (term1380 i s f)). Qed.
Lemma lem5427850 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5427851 (i : type1003) (f : nat -> nat) (s : nat -> Prop) (j : nat) : (term1382 i s f j) = (term1383 i f s j).
Proof. exact (MK_COMB (@lem5427849 i f s) (@lem5427850 j)). Qed.
Lemma lem5427852 (i : type1003) (j : nat) (f : nat -> nat) (s : nat -> Prop) : (term1383 i f s j) = (term1384 i j f s).
Proof. exact (eq_refl (term1383 i f s j)). Qed.
Lemma lem5427853 (i : type1003) (j : nat) (f : nat -> nat) (s : nat -> Prop) : (term1382 i s f j) = (term1384 i j f s).
Proof. exact (TRANS (@lem5427851 i f s j) (@lem5427852 i j f s)). Qed.
Lemma lem5427854 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1385 i s f) = (term1381 i f s).
Proof. exact (fun_ext (fun j : nat => @lem5427853 i j f s)). Qed.
Lemma lem5427855 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5427856 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1386 i s f) = (term1369 i f s).
Proof. exact (MK_COMB (@lem5427855) (@lem5427854 i f s)). Qed.
Lemma lem5427857 (i : type1003) (s : nat -> Prop) : (term1387 i s) = (term1371 i s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427856 i f s)). Qed.
Lemma lem5427858 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427859 (i : type1003) (s : nat -> Prop) : (term1377 i s) = (term1373 i s).
Proof. exact (MK_COMB (@lem5427858) (@lem5427857 i s)). Qed.
Lemma lem5427860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427861 (i : type1003) (s : nat -> Prop) : (term1388 i s) = (term1389 i s).
Proof. exact (MK_COMB (@lem5427860) (@lem5427859 i s)). Qed.
Lemma lem5427862 (i : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1380 i s f) = (term1381 i f s).
Proof. exact (eq_refl (term1380 i s f)). Qed.
Lemma lem5427863 (j : type1003) (f : nat -> nat) : (j f) = (j f).
Proof. exact (eq_refl (j f)). Qed.
Lemma lem5427864 (i : type1003) (s : nat -> Prop) (j : type1003) (f : nat -> nat) : (term1390 i s j f) = (term1391 i s j f).
Proof. exact (MK_COMB (@lem5427862 i f s) (@lem5427863 j f)). Qed.
Lemma lem5427865 (i : type1003) (j : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1391 i s j f) = (term1392 i j f s).
Proof. exact (eq_refl (term1391 i s j f)). Qed.
Lemma lem5427866 (i : type1003) (j : type1003) (f : nat -> nat) (s : nat -> Prop) : (term1390 i s j f) = (term1392 i j f s).
Proof. exact (TRANS (@lem5427864 i s j f) (@lem5427865 i j f s)). Qed.
Lemma lem5427867 (i : type1003) (j : type1003) (s : nat -> Prop) : (term1393 i s j) = (term1394 i j s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5427866 i j f s)). Qed.
Lemma lem5427868 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem5427869 (i : type1003) (j : type1003) (s : nat -> Prop) : (term1395 i s j) = (term1396 i j s).
Proof. exact (MK_COMB (@lem5427868) (@lem5427867 i j s)). Qed.
Lemma lem5427870 (i : type1003) (s : nat -> Prop) : (term1397 i s) = (term1398 i s).
Proof. exact (fun_ext (fun j : type1003 => @lem5427869 i j s)). Qed.
Lemma lem5427871 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427872 (i : type1003) (s : nat -> Prop) : (term1378 i s) = (term1399 i s).
Proof. exact (MK_COMB (@lem5427871) (@lem5427870 i s)). Qed.
Lemma lem5427873 (i : type1003) (s : nat -> Prop) : ((term1377 i s) = (term1378 i s)) = ((term1373 i s) = (term1399 i s)).
Proof. exact (MK_COMB (@lem5427861 i s) (@lem5427872 i s)). Qed.
Lemma lem5427874 (i : type1003) (s : nat -> Prop) : (term1373 i s) = (term1399 i s).
Proof. exact (EQ_MP (@lem5427873 i s) (@lem5427848 i s)). Qed.
Lemma lem5427875 (s : nat -> Prop) : (term1375 s) = (term1400 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427874 i s)). Qed.
Lemma lem5427876 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427877 (s : nat -> Prop) : (term1376 s) = (term1401 s).
Proof. exact (MK_COMB (@lem5427876) (@lem5427875 s)). Qed.
Lemma lem5427878 (s : nat -> Prop) : (term1353 s) = (term1401 s).
Proof. exact (TRANS (@lem5427844 s) (@lem5427877 s)). Qed.
Lemma lem5427879 (s : nat -> Prop) : (term1283 s) = (term1401 s).
Proof. exact (TRANS (@lem5427814 s) (@lem5427878 s)). Qed.
Lemma lem5427880 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427881 (s : nat -> Prop) : (term1291 s) = (term1402 s).
Proof. exact (MK_COMB (@lem5427880 s) (@lem5427879 s)). Qed.
Lemma lem5427883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427884 (P : Prop) (Q : type254) : (term1403 P Q) = (term1404 P Q).
Proof. exact (@lem5427883 type1003 P Q). Qed.
Lemma lem5427885 (s : nat -> Prop) : (term1405 s) = (term1406 s).
Proof. exact (@lem5427884 (@FINITE nat s) (term1400 s)). Qed.
Lemma lem5427886 (i : type1003) (s : nat -> Prop) : (term1407 s i) = (term1399 i s).
Proof. exact (eq_refl (term1407 s i)). Qed.
Lemma lem5427887 (s : nat -> Prop) : (term1408 s) = (term1400 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427886 i s)). Qed.
Lemma lem5427888 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427889 (s : nat -> Prop) : (term1409 s) = (term1401 s).
Proof. exact (MK_COMB (@lem5427888) (@lem5427887 s)). Qed.
Lemma lem5427890 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427891 (s : nat -> Prop) : (term1405 s) = (term1402 s).
Proof. exact (MK_COMB (@lem5427890 s) (@lem5427889 s)). Qed.
Lemma lem5427892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427893 (s : nat -> Prop) : (term1410 s) = (term1411 s).
Proof. exact (MK_COMB (@lem5427892) (@lem5427891 s)). Qed.
Lemma lem5427894 (i : type1003) (s : nat -> Prop) : (term1407 s i) = (term1399 i s).
Proof. exact (eq_refl (term1407 s i)). Qed.
Lemma lem5427895 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427896 (i : type1003) (s : nat -> Prop) : (term1412 s i) = (term1413 i s).
Proof. exact (MK_COMB (@lem5427895 s) (@lem5427894 i s)). Qed.
Lemma lem5427897 (s : nat -> Prop) : (term1414 s) = (term1415 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427896 i s)). Qed.
Lemma lem5427898 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427899 (s : nat -> Prop) : (term1406 s) = (term1416 s).
Proof. exact (MK_COMB (@lem5427898) (@lem5427897 s)). Qed.
Lemma lem5427900 (s : nat -> Prop) : ((term1405 s) = (term1406 s)) = ((term1402 s) = (term1416 s)).
Proof. exact (MK_COMB (@lem5427893 s) (@lem5427899 s)). Qed.
Lemma lem5427901 (s : nat -> Prop) : (term1402 s) = (term1416 s).
Proof. exact (EQ_MP (@lem5427900 s) (@lem5427885 s)). Qed.
Lemma lem5427903 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427904 (P : Prop) (Q : type254) : (term1403 P Q) = (term1404 P Q).
Proof. exact (@lem5427903 type1003 P Q). Qed.
Lemma lem5427905 (i : type1003) (s : nat -> Prop) : (term1417 i s) = (term1418 i s).
Proof. exact (@lem5427904 (@FINITE nat s) (term1398 i s)). Qed.
Lemma lem5427906 (i : type1003) (j : type1003) (s : nat -> Prop) : (term1419 i s j) = (term1396 i j s).
Proof. exact (eq_refl (term1419 i s j)). Qed.
Lemma lem5427907 (i : type1003) (s : nat -> Prop) : (term1420 i s) = (term1398 i s).
Proof. exact (fun_ext (fun j : type1003 => @lem5427906 i j s)). Qed.
Lemma lem5427908 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427909 (i : type1003) (s : nat -> Prop) : (term1421 i s) = (term1399 i s).
Proof. exact (MK_COMB (@lem5427908) (@lem5427907 i s)). Qed.
Lemma lem5427910 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427911 (i : type1003) (s : nat -> Prop) : (term1417 i s) = (term1413 i s).
Proof. exact (MK_COMB (@lem5427910 s) (@lem5427909 i s)). Qed.
Lemma lem5427912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427913 (i : type1003) (s : nat -> Prop) : (term1422 i s) = (term1423 i s).
Proof. exact (MK_COMB (@lem5427912) (@lem5427911 i s)). Qed.
Lemma lem5427914 (i : type1003) (j : type1003) (s : nat -> Prop) : (term1419 i s j) = (term1396 i j s).
Proof. exact (eq_refl (term1419 i s j)). Qed.
Lemma lem5427915 (s : nat -> Prop) : (term1289 s) = (term1289 s).
Proof. exact (eq_refl (term1289 s)). Qed.
Lemma lem5427916 (i : type1003) (j : type1003) (s : nat -> Prop) : (term1424 i s j) = (term1425 i j s).
Proof. exact (MK_COMB (@lem5427915 s) (@lem5427914 i j s)). Qed.
Lemma lem5427917 (i : type1003) (s : nat -> Prop) : (term1426 i s) = (term1427 i s).
Proof. exact (fun_ext (fun j : type1003 => @lem5427916 i j s)). Qed.
Lemma lem5427918 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427919 (i : type1003) (s : nat -> Prop) : (term1418 i s) = (term1428 i s).
Proof. exact (MK_COMB (@lem5427918) (@lem5427917 i s)). Qed.
Lemma lem5427920 (i : type1003) (s : nat -> Prop) : ((term1417 i s) = (term1418 i s)) = ((term1413 i s) = (term1428 i s)).
Proof. exact (MK_COMB (@lem5427913 i s) (@lem5427919 i s)). Qed.
Lemma lem5427921 (i : type1003) (s : nat -> Prop) : (term1413 i s) = (term1428 i s).
Proof. exact (EQ_MP (@lem5427920 i s) (@lem5427905 i s)). Qed.
Lemma lem5427922 (s : nat -> Prop) : (term1415 s) = (term1429 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427921 i s)). Qed.
Lemma lem5427923 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427924 (s : nat -> Prop) : (term1416 s) = (term1430 s).
Proof. exact (MK_COMB (@lem5427923) (@lem5427922 s)). Qed.
Lemma lem5427925 (s : nat -> Prop) : (term1402 s) = (term1430 s).
Proof. exact (TRANS (@lem5427901 s) (@lem5427924 s)). Qed.
Lemma lem5427926 (s : nat -> Prop) : (term1291 s) = (term1430 s).
Proof. exact (TRANS (@lem5427881 s) (@lem5427925 s)). Qed.
Lemma lem5427927 : term1302 = term1431.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427926 s)). Qed.
Lemma lem5427928 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427929 : term1313 = term1432.
Proof. exact (MK_COMB (@lem5427928) (@lem5427927)). Qed.
Lemma lem5427931 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427932 (P : type980) : (term1433 P) = (term1434 P).
Proof. exact (@lem5427931 (nat -> Prop) type1003 P). Qed.
Lemma lem5427933 : term1435 = term1436.
Proof. exact (@lem5427932 term1437). Qed.
Lemma lem5427934 (s : nat -> Prop) : (term1438 s) = (term1429 s).
Proof. exact (eq_refl (term1438 s)). Qed.
Lemma lem5427935 (i : type1003) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5427936 (s : nat -> Prop) (i : type1003) : (term1439 s i) = (term1440 s i).
Proof. exact (MK_COMB (@lem5427934 s) (@lem5427935 i)). Qed.
Lemma lem5427937 (i : type1003) (s : nat -> Prop) : (term1440 s i) = (term1428 i s).
Proof. exact (eq_refl (term1440 s i)). Qed.
Lemma lem5427938 (i : type1003) (s : nat -> Prop) : (term1439 s i) = (term1428 i s).
Proof. exact (TRANS (@lem5427936 s i) (@lem5427937 i s)). Qed.
Lemma lem5427939 (s : nat -> Prop) : (term1441 s) = (term1429 s).
Proof. exact (fun_ext (fun i : type1003 => @lem5427938 i s)). Qed.
Lemma lem5427940 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427941 (s : nat -> Prop) : (term1442 s) = (term1430 s).
Proof. exact (MK_COMB (@lem5427940) (@lem5427939 s)). Qed.
Lemma lem5427942 : term1443 = term1431.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427941 s)). Qed.
Lemma lem5427943 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427944 : term1435 = term1432.
Proof. exact (MK_COMB (@lem5427943) (@lem5427942)). Qed.
Lemma lem5427945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427946 : term1444 = term1445.
Proof. exact (MK_COMB (@lem5427945) (@lem5427944)). Qed.
Lemma lem5427947 (s : nat -> Prop) : (term1438 s) = (term1429 s).
Proof. exact (eq_refl (term1438 s)). Qed.
Lemma lem5427948 (i : type987) (s : nat -> Prop) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem5427949 (i : type987) (s : nat -> Prop) : (term1446 i s) = (term1447 i s).
Proof. exact (MK_COMB (@lem5427947 s) (@lem5427948 i s)). Qed.
Lemma lem5427950 (i : type987) (s : nat -> Prop) : (term1447 i s) = (term1448 i s).
Proof. exact (eq_refl (term1447 i s)). Qed.
Lemma lem5427951 (i : type987) (s : nat -> Prop) : (term1446 i s) = (term1448 i s).
Proof. exact (TRANS (@lem5427949 i s) (@lem5427950 i s)). Qed.
Lemma lem5427952 (i : type987) : (term1449 i) = (term1450 i).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427951 i s)). Qed.
Lemma lem5427953 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427954 (i : type987) : (term1451 i) = (term1452 i).
Proof. exact (MK_COMB (@lem5427953) (@lem5427952 i)). Qed.
Lemma lem5427955 : term1453 = term1454.
Proof. exact (fun_ext (fun i : type987 => @lem5427954 i)). Qed.
Lemma lem5427956 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5427957 : term1436 = term1455.
Proof. exact (MK_COMB (@lem5427956) (@lem5427955)). Qed.
Lemma lem5427958 : (term1435 = term1436) = (term1432 = term1455).
Proof. exact (MK_COMB (@lem5427946) (@lem5427957)). Qed.
Lemma lem5427959 : term1432 = term1455.
Proof. exact (EQ_MP (@lem5427958) (@lem5427933)). Qed.
Lemma lem5427961 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5427962 (P : type980) : (term1433 P) = (term1434 P).
Proof. exact (@lem5427961 (nat -> Prop) type1003 P). Qed.
Lemma lem5427963 (i : type987) : (term1456 i) = (term1457 i).
Proof. exact (@lem5427962 (term1458 i)). Qed.
Lemma lem5427964 (i : type987) (s : nat -> Prop) : (term1459 i s) = (term1460 i s).
Proof. exact (eq_refl (term1459 i s)). Qed.
Lemma lem5427965 (j : type1003) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5427966 (i : type987) (s : nat -> Prop) (j : type1003) : (term1461 i s j) = (term1462 i s j).
Proof. exact (MK_COMB (@lem5427964 i s) (@lem5427965 j)). Qed.
Lemma lem5427967 (i : type987) (j : type1003) (s : nat -> Prop) : (term1462 i s j) = (term1463 i j s).
Proof. exact (eq_refl (term1462 i s j)). Qed.
Lemma lem5427968 (i : type987) (j : type1003) (s : nat -> Prop) : (term1461 i s j) = (term1463 i j s).
Proof. exact (TRANS (@lem5427966 i s j) (@lem5427967 i j s)). Qed.
Lemma lem5427969 (i : type987) (s : nat -> Prop) : (term1464 i s) = (term1460 i s).
Proof. exact (fun_ext (fun j : type1003 => @lem5427968 i j s)). Qed.
Lemma lem5427970 : (@ex ((nat -> nat) -> nat)) = (@ex ((nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat))). Qed.
Lemma lem5427971 (i : type987) (s : nat -> Prop) : (term1465 i s) = (term1448 i s).
Proof. exact (MK_COMB (@lem5427970) (@lem5427969 i s)). Qed.
Lemma lem5427972 (i : type987) : (term1466 i) = (term1450 i).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427971 i s)). Qed.
Lemma lem5427973 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427974 (i : type987) : (term1456 i) = (term1452 i).
Proof. exact (MK_COMB (@lem5427973) (@lem5427972 i)). Qed.
Lemma lem5427975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5427976 (i : type987) : (term1467 i) = (term1468 i).
Proof. exact (MK_COMB (@lem5427975) (@lem5427974 i)). Qed.
Lemma lem5427977 (i : type987) (s : nat -> Prop) : (term1459 i s) = (term1460 i s).
Proof. exact (eq_refl (term1459 i s)). Qed.
Lemma lem5427978 (j : type987) (s : nat -> Prop) : (j s) = (j s).
Proof. exact (eq_refl (j s)). Qed.
Lemma lem5427979 (i : type987) (j : type987) (s : nat -> Prop) : (term1469 i j s) = (term1470 i j s).
Proof. exact (MK_COMB (@lem5427977 i s) (@lem5427978 j s)). Qed.
Lemma lem5427980 (i : type987) (j : type987) (s : nat -> Prop) : (term1470 i j s) = (term1471 i j s).
Proof. exact (eq_refl (term1470 i j s)). Qed.
Lemma lem5427981 (i : type987) (j : type987) (s : nat -> Prop) : (term1469 i j s) = (term1471 i j s).
Proof. exact (TRANS (@lem5427979 i j s) (@lem5427980 i j s)). Qed.
Lemma lem5427982 (i : type987) (j : type987) : (term1472 i j) = (term1473 i j).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5427981 i j s)). Qed.
Lemma lem5427983 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5427984 (i : type987) (j : type987) : (term1474 i j) = (term1475 i j).
Proof. exact (MK_COMB (@lem5427983) (@lem5427982 i j)). Qed.
Lemma lem5427985 (i : type987) : (term1476 i) = (term1477 i).
Proof. exact (fun_ext (fun j : type987 => @lem5427984 i j)). Qed.
Lemma lem5427986 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5427987 (i : type987) : (term1457 i) = (term1478 i).
Proof. exact (MK_COMB (@lem5427986) (@lem5427985 i)). Qed.
Lemma lem5427988 (i : type987) : ((term1456 i) = (term1457 i)) = ((term1452 i) = (term1478 i)).
Proof. exact (MK_COMB (@lem5427976 i) (@lem5427987 i)). Qed.
Lemma lem5427989 (i : type987) : (term1452 i) = (term1478 i).
Proof. exact (EQ_MP (@lem5427988 i) (@lem5427963 i)). Qed.
Lemma lem5427990 : term1454 = term1479.
Proof. exact (fun_ext (fun i : type987 => @lem5427989 i)). Qed.
Lemma lem5427991 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5427992 : term1455 = term1480.
Proof. exact (MK_COMB (@lem5427991) (@lem5427990)). Qed.
Lemma lem5427993 : term1432 = term1480.
Proof. exact (TRANS (@lem5427959) (@lem5427992)). Qed.
Lemma lem5427994 : term1313 = term1480.
Proof. exact (TRANS (@lem5427929) (@lem5427993)). Qed.
Lemma lem5427995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5427996 : term1315 = term1481.
Proof. exact (MK_COMB (@lem5427995) (@lem5427994)). Qed.
Lemma lem5427998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term515 A P Q) = (term516 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5427999 (P : Prop) (Q : type1002) : (term1482 P Q) = (term1483 P Q).
Proof. exact (@lem5427998 (nat -> nat) P Q). Qed.
Lemma lem5428000 (s : nat -> Prop) : (term1484 s) = (term1485 s).
Proof. exact (@lem5427999 (term1486 s) (term1284 s)). Qed.
Lemma lem5428001 (f : nat -> nat) (s : nat -> Prop) : (term1487 s f) = (term1274 f s).
Proof. exact (eq_refl (term1487 s f)). Qed.
Lemma lem5428002 (s : nat -> Prop) : (term1488 s) = (term1284 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5428001 f s)). Qed.
Lemma lem5428003 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5428004 (s : nat -> Prop) : (term1489 s) = (term1285 s).
Proof. exact (MK_COMB (@lem5428003) (@lem5428002 s)). Qed.
Lemma lem5428005 (s : nat -> Prop) : (term1286 s) = (term1286 s).
Proof. exact (eq_refl (term1286 s)). Qed.
Lemma lem5428006 (s : nat -> Prop) : (term1484 s) = (term1288 s).
Proof. exact (MK_COMB (@lem5428005 s) (@lem5428004 s)). Qed.
Lemma lem5428007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5428008 (s : nat -> Prop) : (term1490 s) = (term1491 s).
Proof. exact (MK_COMB (@lem5428007) (@lem5428006 s)). Qed.
Lemma lem5428009 (f : nat -> nat) (s : nat -> Prop) : (term1487 s f) = (term1274 f s).
Proof. exact (eq_refl (term1487 s f)). Qed.
Lemma lem5428010 (s : nat -> Prop) : (term1286 s) = (term1286 s).
Proof. exact (eq_refl (term1286 s)). Qed.
Lemma lem5428011 (f : nat -> nat) (s : nat -> Prop) : (term1492 s f) = (term1493 f s).
Proof. exact (MK_COMB (@lem5428010 s) (@lem5428009 f s)). Qed.
Lemma lem5428012 (s : nat -> Prop) : (term1494 s) = (term1495 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5428011 f s)). Qed.
Lemma lem5428013 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5428014 (s : nat -> Prop) : (term1485 s) = (term1496 s).
Proof. exact (MK_COMB (@lem5428013) (@lem5428012 s)). Qed.
Lemma lem5428015 (s : nat -> Prop) : ((term1484 s) = (term1485 s)) = ((term1288 s) = (term1496 s)).
Proof. exact (MK_COMB (@lem5428008 s) (@lem5428014 s)). Qed.
Lemma lem5428016 (s : nat -> Prop) : (term1288 s) = (term1496 s).
Proof. exact (EQ_MP (@lem5428015 s) (@lem5428000 s)). Qed.
Lemma lem5428017 : term1303 = term1497.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5428016 s)). Qed.
Lemma lem5428018 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5428019 : term1318 = term1498.
Proof. exact (MK_COMB (@lem5428018) (@lem5428017)). Qed.
Lemma lem5428021 {A B : Type'} (P : type1413 A B) : (term297 A B P) = (term298 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5428022 (P : type986) : (term1499 P) = (term1500 P).
Proof. exact (@lem5428021 (nat -> Prop) (nat -> nat) P). Qed.
Lemma lem5428023 : term1501 = term1502.
Proof. exact (@lem5428022 term1503). Qed.
Lemma lem5428024 (s : nat -> Prop) : (term1504 s) = (term1495 s).
Proof. exact (eq_refl (term1504 s)). Qed.
Lemma lem5428025 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5428026 (s : nat -> Prop) (f : nat -> nat) : (term1505 s f) = (term1506 s f).
Proof. exact (MK_COMB (@lem5428024 s) (@lem5428025 f)). Qed.
Lemma lem5428027 (f : nat -> nat) (s : nat -> Prop) : (term1506 s f) = (term1493 f s).
Proof. exact (eq_refl (term1506 s f)). Qed.
Lemma lem5428028 (f : nat -> nat) (s : nat -> Prop) : (term1505 s f) = (term1493 f s).
Proof. exact (TRANS (@lem5428026 s f) (@lem5428027 f s)). Qed.
Lemma lem5428029 (s : nat -> Prop) : (term1507 s) = (term1495 s).
Proof. exact (fun_ext (fun f : nat -> nat => @lem5428028 f s)). Qed.
Lemma lem5428030 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5428031 (s : nat -> Prop) : (term1508 s) = (term1496 s).
Proof. exact (MK_COMB (@lem5428030) (@lem5428029 s)). Qed.
Lemma lem5428032 : term1509 = term1497.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5428031 s)). Qed.
Lemma lem5428033 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5428034 : term1501 = term1498.
Proof. exact (MK_COMB (@lem5428033) (@lem5428032)). Qed.
Lemma lem5428035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5428036 : term1510 = term1511.
Proof. exact (MK_COMB (@lem5428035) (@lem5428034)). Qed.
Lemma lem5428037 (s : nat -> Prop) : (term1504 s) = (term1495 s).
Proof. exact (eq_refl (term1504 s)). Qed.
Lemma lem5428038 (f : type992) (s : nat -> Prop) : (f s) = (f s).
Proof. exact (eq_refl (f s)). Qed.
Lemma lem5428039 (f : type992) (s : nat -> Prop) : (term1512 f s) = (term1513 f s).
Proof. exact (MK_COMB (@lem5428037 s) (@lem5428038 f s)). Qed.
Lemma lem5428040 (f : type992) (s : nat -> Prop) : (term1513 f s) = (term1514 f s).
Proof. exact (eq_refl (term1513 f s)). Qed.
Lemma lem5428041 (f : type992) (s : nat -> Prop) : (term1512 f s) = (term1514 f s).
Proof. exact (TRANS (@lem5428039 f s) (@lem5428040 f s)). Qed.
Lemma lem5428042 (f : type992) : (term1515 f) = (term1516 f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5428041 f s)). Qed.
Lemma lem5428043 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5428044 (f : type992) : (term1517 f) = (term1518 f).
Proof. exact (MK_COMB (@lem5428043) (@lem5428042 f)). Qed.
Lemma lem5428045 : term1519 = term1520.
Proof. exact (fun_ext (fun f : type992 => @lem5428044 f)). Qed.
Lemma lem5428046 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem5428047 : term1502 = term1521.
Proof. exact (MK_COMB (@lem5428046) (@lem5428045)). Qed.
Lemma lem5428048 : (term1501 = term1502) = (term1498 = term1521).
Proof. exact (MK_COMB (@lem5428036) (@lem5428047)). Qed.
Lemma lem5428049 : term1498 = term1521.
Proof. exact (EQ_MP (@lem5428048) (@lem5428023)). Qed.
Lemma lem5428050 : term1318 = term1521.
Proof. exact (TRANS (@lem5428019) (@lem5428049)). Qed.
Lemma lem5428051 : term1319 = term1522.
Proof. exact (MK_COMB (@lem5427996) (@lem5428050)). Qed.
Lemma lem5428053 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5428054 (P : type250) (Q : Prop) : (term1523 P Q) = (term1524 P Q).
Proof. exact (@lem5428053 type987 P Q). Qed.
Lemma lem5428055 : term1525 = term1526.
Proof. exact (@lem5428054 term1479 term1521). Qed.
Lemma lem5428056 (i : type987) : (term1527 i) = (term1478 i).
Proof. exact (eq_refl (term1527 i)). Qed.
Lemma lem5428057 : term1528 = term1479.
Proof. exact (fun_ext (fun i : type987 => @lem5428056 i)). Qed.
Lemma lem5428058 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428059 : term1529 = term1480.
Proof. exact (MK_COMB (@lem5428058) (@lem5428057)). Qed.
Lemma lem5428060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5428061 : term1530 = term1481.
Proof. exact (MK_COMB (@lem5428060) (@lem5428059)). Qed.
Lemma lem5428062 : term1521 = term1521.
Proof. exact (eq_refl term1521). Qed.
Lemma lem5428063 : term1525 = term1522.
Proof. exact (MK_COMB (@lem5428061) (@lem5428062)). Qed.
Lemma lem5428064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5428065 : term1531 = term1532.
Proof. exact (MK_COMB (@lem5428064) (@lem5428063)). Qed.
Lemma lem5428066 (i : type987) : (term1527 i) = (term1478 i).
Proof. exact (eq_refl (term1527 i)). Qed.
Lemma lem5428067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5428068 (i : type987) : (term1533 i) = (term1534 i).
Proof. exact (MK_COMB (@lem5428067) (@lem5428066 i)). Qed.
Lemma lem5428069 : term1521 = term1521.
Proof. exact (eq_refl term1521). Qed.
Lemma lem5428070 (i : type987) : (term1535 i) = (term1536 i).
Proof. exact (MK_COMB (@lem5428068 i) (@lem5428069)). Qed.
Lemma lem5428071 : term1537 = term1538.
Proof. exact (fun_ext (fun i : type987 => @lem5428070 i)). Qed.
Lemma lem5428072 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428073 : term1526 = term1539.
Proof. exact (MK_COMB (@lem5428072) (@lem5428071)). Qed.
Lemma lem5428074 : (term1525 = term1526) = (term1522 = term1539).
Proof. exact (MK_COMB (@lem5428065) (@lem5428073)). Qed.
Lemma lem5428075 : term1522 = term1539.
Proof. exact (EQ_MP (@lem5428074) (@lem5428055)). Qed.
Lemma lem5428077 {A : Type'} (P : A -> Prop) (Q : Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5428078 (P : type250) (Q : Prop) : (term1523 P Q) = (term1524 P Q).
Proof. exact (@lem5428077 type987 P Q). Qed.
Lemma lem5428079 (i : type987) : (term1540 i) = (term1541 i).
Proof. exact (@lem5428078 (term1477 i) term1521). Qed.
Lemma lem5428080 (i : type987) (j : type987) : (term1542 i j) = (term1475 i j).
Proof. exact (eq_refl (term1542 i j)). Qed.
Lemma lem5428081 (i : type987) : (term1543 i) = (term1477 i).
Proof. exact (fun_ext (fun j : type987 => @lem5428080 i j)). Qed.
Lemma lem5428082 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428083 (i : type987) : (term1544 i) = (term1478 i).
Proof. exact (MK_COMB (@lem5428082) (@lem5428081 i)). Qed.
Lemma lem5428084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5428085 (i : type987) : (term1545 i) = (term1534 i).
Proof. exact (MK_COMB (@lem5428084) (@lem5428083 i)). Qed.
Lemma lem5428086 : term1521 = term1521.
Proof. exact (eq_refl term1521). Qed.
Lemma lem5428087 (i : type987) : (term1540 i) = (term1536 i).
Proof. exact (MK_COMB (@lem5428085 i) (@lem5428086)). Qed.
Lemma lem5428088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5428089 (i : type987) : (term1546 i) = (term1547 i).
Proof. exact (MK_COMB (@lem5428088) (@lem5428087 i)). Qed.
Lemma lem5428090 (i : type987) (j : type987) : (term1542 i j) = (term1475 i j).
Proof. exact (eq_refl (term1542 i j)). Qed.
Lemma lem5428091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5428092 (i : type987) (j : type987) : (term1548 i j) = (term1549 i j).
Proof. exact (MK_COMB (@lem5428091) (@lem5428090 i j)). Qed.
Lemma lem5428093 : term1521 = term1521.
Proof. exact (eq_refl term1521). Qed.
Lemma lem5428094 (i : type987) (j : type987) : (term1550 i j) = (term1551 i j).
Proof. exact (MK_COMB (@lem5428092 i j) (@lem5428093)). Qed.
Lemma lem5428095 (i : type987) : (term1552 i) = (term1553 i).
Proof. exact (fun_ext (fun j : type987 => @lem5428094 i j)). Qed.
Lemma lem5428096 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428097 (i : type987) : (term1541 i) = (term1554 i).
Proof. exact (MK_COMB (@lem5428096) (@lem5428095 i)). Qed.
Lemma lem5428098 (i : type987) : ((term1540 i) = (term1541 i)) = ((term1536 i) = (term1554 i)).
Proof. exact (MK_COMB (@lem5428089 i) (@lem5428097 i)). Qed.
Lemma lem5428099 (i : type987) : (term1536 i) = (term1554 i).
Proof. exact (EQ_MP (@lem5428098 i) (@lem5428079 i)). Qed.
Lemma lem5428101 {A : Type'} (P : Prop) (Q : A -> Prop) : (term398 A P Q) = (term399 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5428102 (P : Prop) (Q : type251) : (term1555 P Q) = (term1556 P Q).
Proof. exact (@lem5428101 type992 P Q). Qed.
Lemma lem5428103 (i : type987) (j : type987) : (term1557 i j) = (term1558 i j).
Proof. exact (@lem5428102 (term1475 i j) term1520). Qed.
Lemma lem5428104 (f : type992) : (term1559 f) = (term1518 f).
Proof. exact (eq_refl (term1559 f)). Qed.
Lemma lem5428105 : term1560 = term1520.
Proof. exact (fun_ext (fun f : type992 => @lem5428104 f)). Qed.
Lemma lem5428106 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem5428107 : term1561 = term1521.
Proof. exact (MK_COMB (@lem5428106) (@lem5428105)). Qed.
Lemma lem5428108 (i : type987) (j : type987) : (term1549 i j) = (term1549 i j).
Proof. exact (eq_refl (term1549 i j)). Qed.
Lemma lem5428109 (i : type987) (j : type987) : (term1557 i j) = (term1551 i j).
Proof. exact (MK_COMB (@lem5428108 i j) (@lem5428107)). Qed.
Lemma lem5428110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5428111 (i : type987) (j : type987) : (term1562 i j) = (term1563 i j).
Proof. exact (MK_COMB (@lem5428110) (@lem5428109 i j)). Qed.
Lemma lem5428112 (f : type992) : (term1559 f) = (term1518 f).
Proof. exact (eq_refl (term1559 f)). Qed.
Lemma lem5428113 (i : type987) (j : type987) : (term1549 i j) = (term1549 i j).
Proof. exact (eq_refl (term1549 i j)). Qed.
Lemma lem5428114 (i : type987) (j : type987) (f : type992) : (term1564 i j f) = (term1565 i j f).
Proof. exact (MK_COMB (@lem5428113 i j) (@lem5428112 f)). Qed.
Lemma lem5428115 (i : type987) (j : type987) : (term1566 i j) = (term1567 i j).
Proof. exact (fun_ext (fun f : type992 => @lem5428114 i j f)). Qed.
Lemma lem5428116 : (@ex ((nat -> Prop) -> nat -> nat)) = (@ex ((nat -> Prop) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat -> nat))). Qed.
Lemma lem5428117 (i : type987) (j : type987) : (term1558 i j) = (term1568 i j).
Proof. exact (MK_COMB (@lem5428116) (@lem5428115 i j)). Qed.
Lemma lem5428118 (i : type987) (j : type987) : ((term1557 i j) = (term1558 i j)) = ((term1551 i j) = (term1568 i j)).
Proof. exact (MK_COMB (@lem5428111 i j) (@lem5428117 i j)). Qed.
Lemma lem5428119 (i : type987) (j : type987) : (term1551 i j) = (term1568 i j).
Proof. exact (EQ_MP (@lem5428118 i j) (@lem5428103 i j)). Qed.
Lemma lem5428120 (i : type987) : (term1553 i) = (term1569 i).
Proof. exact (fun_ext (fun j : type987 => @lem5428119 i j)). Qed.
Lemma lem5428121 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428122 (i : type987) : (term1554 i) = (term1570 i).
Proof. exact (MK_COMB (@lem5428121) (@lem5428120 i)). Qed.
Lemma lem5428123 (i : type987) : (term1536 i) = (term1570 i).
Proof. exact (TRANS (@lem5428099 i) (@lem5428122 i)). Qed.
Lemma lem5428124 : term1538 = term1571.
Proof. exact (fun_ext (fun i : type987 => @lem5428123 i)). Qed.
Lemma lem5428125 : (@ex ((nat -> Prop) -> (nat -> nat) -> nat)) = (@ex ((nat -> Prop) -> (nat -> nat) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> (nat -> nat) -> nat))). Qed.
Lemma lem5428126 : term1539 = term1572.
Proof. exact (MK_COMB (@lem5428125) (@lem5428124)). Qed.
Lemma lem5428127 : term1522 = term1572.
Proof. exact (TRANS (@lem5428075) (@lem5428126)). Qed.
Lemma lem5428128 : term1319 = term1572.
Proof. exact (TRANS (@lem5428051) (@lem5428127)). Qed.
Lemma lem5428129 : term1297 = term1572.
Proof. exact (TRANS (@lem5427483) (@lem5428128)). Qed.
Lemma lem5428130 : term12 = term1572.
Proof. exact (TRANS (@lem5427456) (@lem5428129)). Qed.
Lemma lem5428131 (h1 : term12) : term1572.
Proof. exact (EQ_MP (@lem5428130) (@lem5424292 h1)). Qed.
Lemma lem5428132 (i : type987) (h1 : term1570 i) : term1570 i.
Proof. exact (h1). Qed.
Lemma lem5428133 (i : type987) (j : type987) (h1 : term1568 i j) : term1568 i j.
Proof. exact (h1). Qed.
Lemma lem5428135 {A : Type'} (i' : type177 A) (h1 : term1231 A i') : term1231 A i'.
Proof. exact (h1). Qed.
Lemma lem5428136 {A : Type'} (i' : type177 A) (j' : type177 A) (h1 : term1229 A i' j') : term1229 A i' j'.
Proof. exact (h1). Qed.
Lemma lem5428138 {A : Type'} (i'' : type661 A) (h1 : term892 A i'') : term892 A i''.
Proof. exact (h1). Qed.
Lemma lem5428139 {A : Type'} (i'' : type661 A) (j'' : type661 A) (h1 : term890 A i'' j'') : term890 A i'' j''.
Proof. exact (h1). Qed.
Lemma lem5428140 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term887 A i'' j'' f''.
Proof. exact (h1). Qed.
Lemma lem5428141 {A : Type'} (s : A -> Prop) (h1 : term550 A s) : term550 A s.
Proof. exact (h1). Qed.
Lemma lem5428142 {A : Type'} (i''' : type984 A) (s : A -> Prop) (h1 : term548 A i''' s) : term548 A i''' s.
Proof. exact (h1). Qed.
Lemma lem5428143 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term546 A i''' j''' s) : term546 A i''' j''' s.
Proof. exact (h1). Qed.
Lemma lem5428144 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) (h1 : term544 A i''' j''' s k) : term544 A i''' j''' s k.
Proof. exact (h1). Qed.
Lemma lem5428145 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term541 A i''' j''' s f''' k) : term541 A i''' j''' s f''' k.
Proof. exact (h1). Qed.
Lemma lem5428366 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5428373 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428374 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5428373 (nat -> A) (type989 A) f x). Qed.
Lemma lem5428375 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f).
Proof. exact (@lem5428374 A (@IMAGE nat A) f). Qed.
Lemma lem5428376 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5428377 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@IMAGE nat A f s) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f s).
Proof. exact (MK_COMB (@lem5428375 A f) (@lem5428376 s)). Qed.
Lemma lem5428379 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428380 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5428379 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem5428381 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f s) = (term1573 A f s).
Proof. exact (@lem5428380 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f) s). Qed.
Lemma lem5428383 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@IMAGE nat A f s) = (term1573 A f s).
Proof. exact (TRANS (@lem5428377 A f s) (@lem5428381 A f s)). Qed.
Lemma lem5428384 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term554 A f s) = (term1574 A f s).
Proof. exact (MK_COMB (@lem5428366 A) (@lem5428383 A f s)). Qed.
Lemma lem5428386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428387 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5428386 (A -> Prop) Prop f x). Qed.
Lemma lem5428388 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1574 A f s) = (term1575 A f s).
Proof. exact (@lem5428387 A (@FINITE A) (term1573 A f s)). Qed.
Lemma lem5428389 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term554 A f s) = (term1575 A f s).
Proof. exact (TRANS (@lem5428384 A f s) (@lem5428388 A f s)). Qed.
Lemma lem5428390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5428395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428396 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5428395 (nat -> Prop) Prop f x). Qed.
Lemma lem5428398 (s : nat -> Prop) : (@FINITE nat s) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) s).
Proof. exact (@lem5428396 (@FINITE nat) s). Qed.
Lemma lem5428399 (s : nat -> Prop) : (term1486 s) = (term1576 s).
Proof. exact (MK_COMB (@lem5428390) (@lem5428398 s)). Qed.
Lemma lem5428400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5428401 (s : nat -> Prop) : (term1286 s) = (term1577 s).
Proof. exact (MK_COMB (@lem5428400) (@lem5428399 s)). Qed.
Lemma lem5428402 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term553 A f s) = (term1578 A f s).
Proof. exact (MK_COMB (@lem5428401 s) (@lem5428389 A f s)). Qed.
Lemma lem5428403 {A : Type'} (f : nat -> A) : (term555 A f) = (term1579 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5428402 A f s)). Qed.
Lemma lem5428404 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5428405 {A : Type'} (f : nat -> A) : (term556 A f) = (term1580 A f).
Proof. exact (MK_COMB (@lem5428404) (@lem5428403 A f)). Qed.
Lemma lem5428406 {A : Type'} : (term557 A) = (term1581 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5428405 A f)). Qed.
Lemma lem5428407 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5428408 {A : Type'} : (term558 A) = (term1582 A).
Proof. exact (MK_COMB (@lem5428407 A) (@lem5428406 A)). Qed.
Lemma lem5428409 {A : Type'} (h1 : term15 A) : term1582 A.
Proof. exact (EQ_MP (@lem5428408 A) (@lem5425579 A h1)). Qed.
Lemma lem5428542 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem5428549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428550 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5428549 nat type1605 f x). Qed.
Lemma lem5428551 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem5428550 dotdot m). Qed.
Lemma lem5428552 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5428553 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem5428551 m) (@lem5428552 n)). Qed.
Lemma lem5428555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428556 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5428555 nat (nat -> Prop) f x). Qed.
Lemma lem5428557 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term1583 m n).
Proof. exact (@lem5428556 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem5428559 (m : nat) (n : nat) : (dotdot m n) = (term1583 m n).
Proof. exact (TRANS (@lem5428553 m n) (@lem5428557 m n)). Qed.
Lemma lem5428560 (m : nat) (n : nat) : (term101 m n) = (term1584 m n).
Proof. exact (MK_COMB (@lem5428542) (@lem5428559 m n)). Qed.
Lemma lem5428562 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5428563 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5428562 (nat -> Prop) Prop f x). Qed.
Lemma lem5428564 (m : nat) (n : nat) : (term1584 m n) = (term1585 m n).
Proof. exact (@lem5428563 (@FINITE nat) (term1583 m n)). Qed.
Lemma lem5428565 (m : nat) (n : nat) : (term101 m n) = (term1585 m n).
Proof. exact (TRANS (@lem5428560 m n) (@lem5428564 m n)). Qed.
Lemma lem5428566 (m : nat) : (term102 m) = (term1586 m).
Proof. exact (fun_ext (fun n : nat => @lem5428565 m n)). Qed.
Lemma lem5428567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5428568 (m : nat) : (term103 m) = (term1587 m).
Proof. exact (MK_COMB (@lem5428567) (@lem5428566 m)). Qed.
Lemma lem5428569 : term104 = term1588.
Proof. exact (fun_ext (fun m : nat => @lem5428568 m)). Qed.
Lemma lem5428570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5428571 : term105 = term1589.
Proof. exact (MK_COMB (@lem5428570) (@lem5428569)). Qed.
Lemma lem5428572 (h1 : term105) : term1589.
Proof. exact (EQ_MP (@lem5428571) (@lem5425809 h1)). Qed.
Lemma lem5429731 {A : Type'} : (@IMAGE nat A) = (@IMAGE nat A).
Proof. exact (eq_refl (@IMAGE nat A)). Qed.
Lemma lem5429736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429737 {A : Type'} (f : type681 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> A) f x).
Proof. exact (@lem5429736 (A -> Prop) (nat -> A) f x). Qed.
Lemma lem5429739 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (f'' s) = (@I ((A -> Prop) -> nat -> A) f'' s).
Proof. exact (@lem5429737 A f'' s). Qed.
Lemma lem5429740 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5429741 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5429746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429747 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429746 nat nat f x). Qed.
Lemma lem5429749 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5429747 BIT1 0). Qed.
Lemma lem5429750 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5429741) (@lem5429749)). Qed.
Lemma lem5429752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429753 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429752 nat nat f x). Qed.
Lemma lem5429754 : term1591 = term1592.
Proof. exact (@lem5429753 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5429755 : term1590 = term1592.
Proof. exact (TRANS (@lem5429750) (@lem5429754)). Qed.
Lemma lem5429760 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429761 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5429760 (A -> Prop) nat f x). Qed.
Lemma lem5429763 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5429761 A (@CARD A) s). Qed.
Lemma lem5429764 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5429740) (@lem5429755)). Qed.
Lemma lem5429765 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5429764) (@lem5429763 A s)). Qed.
Lemma lem5429767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429768 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5429767 nat type1605 f x). Qed.
Lemma lem5429769 : term1594 = term1597.
Proof. exact (@lem5429768 dotdot term1592). Qed.
Lemma lem5429770 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429771 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5429769) (@lem5429770 A s)). Qed.
Lemma lem5429773 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429774 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5429773 nat (nat -> Prop) f x). Qed.
Lemma lem5429775 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5429774 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429776 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429771 A s) (@lem5429775 A s)). Qed.
Lemma lem5429777 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429765 A s) (@lem5429776 A s)). Qed.
Lemma lem5429778 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1600 A f'' s) = (term1601 A f'' s).
Proof. exact (MK_COMB (@lem5429731 A) (@lem5429739 A f'' s)). Qed.
Lemma lem5429779 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1602 A f'' s) = (term1603 A f'' s).
Proof. exact (MK_COMB (@lem5429778 A f'' s) (@lem5429777 A s)). Qed.
Lemma lem5429781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429782 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5429781 (nat -> A) (type989 A) f x). Qed.
Lemma lem5429783 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1601 A f'' s) = (term1604 A f'' s).
Proof. exact (@lem5429782 A (@IMAGE nat A) (@I ((A -> Prop) -> nat -> A) f'' s)). Qed.
Lemma lem5429784 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5429785 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1603 A f'' s) = (term1605 A f'' s).
Proof. exact (MK_COMB (@lem5429783 A f'' s) (@lem5429784 A s)). Qed.
Lemma lem5429787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429788 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5429787 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem5429789 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1605 A f'' s) = (term1606 A f'' s).
Proof. exact (@lem5429788 A (term1604 A f'' s) (term1599 A s)). Qed.
Lemma lem5429790 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1603 A f'' s) = (term1606 A f'' s).
Proof. exact (TRANS (@lem5429785 A f'' s) (@lem5429789 A f'' s)). Qed.
Lemma lem5429791 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1602 A f'' s) = (term1606 A f'' s).
Proof. exact (TRANS (@lem5429779 A f'' s) (@lem5429790 A f'' s)). Qed.
Lemma lem5429792 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem5429793 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (s = (term1602 A f'' s)) = (s = (term1606 A f'' s)).
Proof. exact (MK_COMB (@lem5429792 A s) (@lem5429791 A f'' s)). Qed.
Lemma lem5429798 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5429799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5429800 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5429807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429808 {A : Type'} (f : type681 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> A) f x).
Proof. exact (@lem5429807 (A -> Prop) (nat -> A) f x). Qed.
Lemma lem5429809 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (f'' s) = (@I ((A -> Prop) -> nat -> A) f'' s).
Proof. exact (@lem5429808 A f'' s). Qed.
Lemma lem5429810 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5429811 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (f'' s i) = (@I ((A -> Prop) -> nat -> A) f'' s i).
Proof. exact (MK_COMB (@lem5429809 A f'' s) (@lem5429810 i)). Qed.
Lemma lem5429813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429814 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5429813 nat A f x). Qed.
Lemma lem5429815 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (@I ((A -> Prop) -> nat -> A) f'' s i) = (term1607 A f'' s i).
Proof. exact (@lem5429814 A (@I ((A -> Prop) -> nat -> A) f'' s) i). Qed.
Lemma lem5429817 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (f'' s i) = (term1607 A f'' s i).
Proof. exact (TRANS (@lem5429811 A f'' s i) (@lem5429815 A f'' s i)). Qed.
Lemma lem5429824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429825 {A : Type'} (f : type681 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> A) f x).
Proof. exact (@lem5429824 (A -> Prop) (nat -> A) f x). Qed.
Lemma lem5429826 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (f'' s) = (@I ((A -> Prop) -> nat -> A) f'' s).
Proof. exact (@lem5429825 A f'' s). Qed.
Lemma lem5429827 (j : nat) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5429828 {A : Type'} (f'' : type681 A) (s : A -> Prop) (j : nat) : (f'' s j) = (@I ((A -> Prop) -> nat -> A) f'' s j).
Proof. exact (MK_COMB (@lem5429826 A f'' s) (@lem5429827 j)). Qed.
Lemma lem5429830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429831 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5429830 nat A f x). Qed.
Lemma lem5429832 {A : Type'} (f'' : type681 A) (s : A -> Prop) (j : nat) : (@I ((A -> Prop) -> nat -> A) f'' s j) = (term1607 A f'' s j).
Proof. exact (@lem5429831 A (@I ((A -> Prop) -> nat -> A) f'' s) j). Qed.
Lemma lem5429834 {A : Type'} (f'' : type681 A) (s : A -> Prop) (j : nat) : (f'' s j) = (term1607 A f'' s j).
Proof. exact (TRANS (@lem5429828 A f'' s j) (@lem5429832 A f'' s j)). Qed.
Lemma lem5429835 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1608 A f'' s i) = (term1609 A f'' s i).
Proof. exact (MK_COMB (@lem5429800 A) (@lem5429817 A f'' s i)). Qed.
Lemma lem5429836 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) (j : nat) : ((f'' s i) = (f'' s j)) = ((term1607 A f'' s i) = (term1607 A f'' s j)).
Proof. exact (MK_COMB (@lem5429835 A f'' s i) (@lem5429834 A f'' s j)). Qed.
Lemma lem5429837 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) (j : nat) : (term1610 A i f'' s j) = (term1611 A i f'' s j).
Proof. exact (MK_COMB (@lem5429799) (@lem5429836 A i f'' s j)). Qed.
Lemma lem5429838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5429841 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5429842 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5429847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429848 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429847 nat nat f x). Qed.
Lemma lem5429850 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5429848 BIT1 0). Qed.
Lemma lem5429851 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5429842) (@lem5429850)). Qed.
Lemma lem5429853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429854 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429853 nat nat f x). Qed.
Lemma lem5429855 : term1591 = term1592.
Proof. exact (@lem5429854 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5429856 : term1590 = term1592.
Proof. exact (TRANS (@lem5429851) (@lem5429855)). Qed.
Lemma lem5429861 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429862 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5429861 (A -> Prop) nat f x). Qed.
Lemma lem5429864 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5429862 A (@CARD A) s). Qed.
Lemma lem5429865 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5429841) (@lem5429856)). Qed.
Lemma lem5429866 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5429865) (@lem5429864 A s)). Qed.
Lemma lem5429868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429869 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5429868 nat type1605 f x). Qed.
Lemma lem5429870 : term1594 = term1597.
Proof. exact (@lem5429869 dotdot term1592). Qed.
Lemma lem5429871 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429872 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5429870) (@lem5429871 A s)). Qed.
Lemma lem5429874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429875 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5429874 nat (nat -> Prop) f x). Qed.
Lemma lem5429876 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5429875 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429877 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429872 A s) (@lem5429876 A s)). Qed.
Lemma lem5429878 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429866 A s) (@lem5429877 A s)). Qed.
Lemma lem5429879 (j : nat) : (@IN nat j) = (@IN nat j).
Proof. exact (eq_refl (@IN nat j)). Qed.
Lemma lem5429880 {A : Type'} (j : nat) (s : A -> Prop) : (term561 A j s) = (term1612 A j s).
Proof. exact (MK_COMB (@lem5429879 j) (@lem5429878 A s)). Qed.
Lemma lem5429882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429883 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5429882 nat type993 f x). Qed.
Lemma lem5429884 (j : nat) : (@IN nat j) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j).
Proof. exact (@lem5429883 (@IN nat) j). Qed.
Lemma lem5429885 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5429886 {A : Type'} (j : nat) (s : A -> Prop) : (term1612 A j s) = (term1613 A j s).
Proof. exact (MK_COMB (@lem5429884 j) (@lem5429885 A s)). Qed.
Lemma lem5429888 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429889 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5429888 (nat -> Prop) Prop f x). Qed.
Lemma lem5429890 {A : Type'} (j : nat) (s : A -> Prop) : (term1613 A j s) = (term1614 A j s).
Proof. exact (@lem5429889 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j) (term1599 A s)). Qed.
Lemma lem5429891 {A : Type'} (j : nat) (s : A -> Prop) : (term1612 A j s) = (term1614 A j s).
Proof. exact (TRANS (@lem5429886 A j s) (@lem5429890 A j s)). Qed.
Lemma lem5429892 {A : Type'} (j : nat) (s : A -> Prop) : (term561 A j s) = (term1614 A j s).
Proof. exact (TRANS (@lem5429880 A j s) (@lem5429891 A j s)). Qed.
Lemma lem5429893 {A : Type'} (j : nat) (s : A -> Prop) : (term1615 A j s) = (term1616 A j s).
Proof. exact (MK_COMB (@lem5429838) (@lem5429892 A j s)). Qed.
Lemma lem5429894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5429895 {A : Type'} (j : nat) (s : A -> Prop) : (term562 A j s) = (term1617 A j s).
Proof. exact (MK_COMB (@lem5429894) (@lem5429893 A j s)). Qed.
Lemma lem5429896 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) (j : nat) : (term1618 A i f'' s j) = (term1619 A i f'' s j).
Proof. exact (MK_COMB (@lem5429895 A j s) (@lem5429837 A i f'' s j)). Qed.
Lemma lem5429897 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5429900 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5429901 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5429906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429907 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429906 nat nat f x). Qed.
Lemma lem5429909 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5429907 BIT1 0). Qed.
Lemma lem5429910 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5429901) (@lem5429909)). Qed.
Lemma lem5429912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429913 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429912 nat nat f x). Qed.
Lemma lem5429914 : term1591 = term1592.
Proof. exact (@lem5429913 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5429915 : term1590 = term1592.
Proof. exact (TRANS (@lem5429910) (@lem5429914)). Qed.
Lemma lem5429920 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429921 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5429920 (A -> Prop) nat f x). Qed.
Lemma lem5429923 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5429921 A (@CARD A) s). Qed.
Lemma lem5429924 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5429900) (@lem5429915)). Qed.
Lemma lem5429925 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5429924) (@lem5429923 A s)). Qed.
Lemma lem5429927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429928 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5429927 nat type1605 f x). Qed.
Lemma lem5429929 : term1594 = term1597.
Proof. exact (@lem5429928 dotdot term1592). Qed.
Lemma lem5429930 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429931 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5429929) (@lem5429930 A s)). Qed.
Lemma lem5429933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429934 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5429933 nat (nat -> Prop) f x). Qed.
Lemma lem5429935 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5429934 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5429936 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429931 A s) (@lem5429935 A s)). Qed.
Lemma lem5429937 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5429925 A s) (@lem5429936 A s)). Qed.
Lemma lem5429938 (i : nat) : (@IN nat i) = (@IN nat i).
Proof. exact (eq_refl (@IN nat i)). Qed.
Lemma lem5429939 {A : Type'} (i : nat) (s : A -> Prop) : (term561 A i s) = (term1612 A i s).
Proof. exact (MK_COMB (@lem5429938 i) (@lem5429937 A s)). Qed.
Lemma lem5429941 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429942 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5429941 nat type993 f x). Qed.
Lemma lem5429943 (i : nat) : (@IN nat i) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i).
Proof. exact (@lem5429942 (@IN nat) i). Qed.
Lemma lem5429944 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5429945 {A : Type'} (i : nat) (s : A -> Prop) : (term1612 A i s) = (term1613 A i s).
Proof. exact (MK_COMB (@lem5429943 i) (@lem5429944 A s)). Qed.
Lemma lem5429947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429948 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5429947 (nat -> Prop) Prop f x). Qed.
Lemma lem5429949 {A : Type'} (i : nat) (s : A -> Prop) : (term1613 A i s) = (term1614 A i s).
Proof. exact (@lem5429948 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i) (term1599 A s)). Qed.
Lemma lem5429950 {A : Type'} (i : nat) (s : A -> Prop) : (term1612 A i s) = (term1614 A i s).
Proof. exact (TRANS (@lem5429945 A i s) (@lem5429949 A i s)). Qed.
Lemma lem5429951 {A : Type'} (i : nat) (s : A -> Prop) : (term561 A i s) = (term1614 A i s).
Proof. exact (TRANS (@lem5429939 A i s) (@lem5429950 A i s)). Qed.
Lemma lem5429952 {A : Type'} (i : nat) (s : A -> Prop) : (term1615 A i s) = (term1616 A i s).
Proof. exact (MK_COMB (@lem5429897) (@lem5429951 A i s)). Qed.
Lemma lem5429953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5429954 {A : Type'} (i : nat) (s : A -> Prop) : (term562 A i s) = (term1617 A i s).
Proof. exact (MK_COMB (@lem5429953) (@lem5429952 A i s)). Qed.
Lemma lem5429955 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) (j : nat) : (term1620 A i f'' s j) = (term1621 A i f'' s j).
Proof. exact (MK_COMB (@lem5429954 A i s) (@lem5429896 A i f'' s j)). Qed.
Lemma lem5429956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5429957 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) (j : nat) : (term1622 A i f'' s j) = (term1623 A i f'' s j).
Proof. exact (MK_COMB (@lem5429956) (@lem5429955 A i f'' s j)). Qed.
Lemma lem5429958 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) (j : nat) : (term1624 A f'' s i j) = (term1625 A f'' s i j).
Proof. exact (MK_COMB (@lem5429957 A i f'' s j) (@lem5429798 i j)). Qed.
Lemma lem5429959 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1626 A f'' s i) = (term1627 A f'' s i).
Proof. exact (fun_ext (fun j : nat => @lem5429958 A f'' s i j)). Qed.
Lemma lem5429960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5429961 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1628 A f'' s i) = (term1629 A f'' s i).
Proof. exact (MK_COMB (@lem5429960) (@lem5429959 A f'' s i)). Qed.
Lemma lem5429962 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1630 A f'' s) = (term1631 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5429961 A f'' s i)). Qed.
Lemma lem5429963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5429964 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1632 A f'' s) = (term1633 A f'' s).
Proof. exact (MK_COMB (@lem5429963) (@lem5429962 A f'' s)). Qed.
Lemma lem5429965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5429966 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1634 A f'' s) = (term1635 A f'' s).
Proof. exact (MK_COMB (@lem5429965) (@lem5429964 A f'' s)). Qed.
Lemma lem5429967 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1636 A f'' s) = (term1637 A f'' s).
Proof. exact (MK_COMB (@lem5429966 A f'' s) (@lem5429793 A f'' s)). Qed.
Lemma lem5429968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5429973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429974 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5429973 (A -> Prop) Prop f x). Qed.
Lemma lem5429976 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5429974 A (@FINITE A) s). Qed.
Lemma lem5429977 {A : Type'} (s : A -> Prop) : (term435 A s) = (term1638 A s).
Proof. exact (MK_COMB (@lem5429968) (@lem5429976 A s)). Qed.
Lemma lem5429978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5429979 {A : Type'} (s : A -> Prop) : (term609 A s) = (term1639 A s).
Proof. exact (MK_COMB (@lem5429978) (@lem5429977 A s)). Qed.
Lemma lem5429980 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term834 A f'' s) = (term1640 A f'' s).
Proof. exact (MK_COMB (@lem5429979 A s) (@lem5429967 A f'' s)). Qed.
Lemma lem5429981 {A : Type'} (f'' : type681 A) : (term836 A f'') = (term1641 A f'').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5429980 A f'' s)). Qed.
Lemma lem5429982 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5429983 {A : Type'} (f'' : type681 A) : (term838 A f'') = (term1642 A f'').
Proof. exact (MK_COMB (@lem5429982 A) (@lem5429981 A f'')). Qed.
Lemma lem5429984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5429989 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5429990 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5429995 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5429996 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5429995 nat nat f x). Qed.
Lemma lem5429998 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5429996 BIT1 0). Qed.
Lemma lem5429999 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5429990) (@lem5429998)). Qed.
Lemma lem5430001 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430002 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5430001 nat nat f x). Qed.
Lemma lem5430003 : term1591 = term1592.
Proof. exact (@lem5430002 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5430004 : term1590 = term1592.
Proof. exact (TRANS (@lem5429999) (@lem5430003)). Qed.
Lemma lem5430009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430010 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5430009 (A -> Prop) nat f x). Qed.
Lemma lem5430012 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5430010 A (@CARD A) s). Qed.
Lemma lem5430013 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5429989) (@lem5430004)). Qed.
Lemma lem5430014 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5430013) (@lem5430012 A s)). Qed.
Lemma lem5430016 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430017 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5430016 nat type1605 f x). Qed.
Lemma lem5430018 : term1594 = term1597.
Proof. exact (@lem5430017 dotdot term1592). Qed.
Lemma lem5430019 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430020 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5430018) (@lem5430019 A s)). Qed.
Lemma lem5430022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430023 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5430022 nat (nat -> Prop) f x). Qed.
Lemma lem5430024 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5430023 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430025 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430020 A s) (@lem5430024 A s)). Qed.
Lemma lem5430026 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430014 A s) (@lem5430025 A s)). Qed.
Lemma lem5430027 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@IMAGE nat A f).
Proof. exact (eq_refl (@IMAGE nat A f)). Qed.
Lemma lem5430028 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term89 A f s) = (term1643 A f s).
Proof. exact (MK_COMB (@lem5430027 A f) (@lem5430026 A s)). Qed.
Lemma lem5430030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430031 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430030 (nat -> A) (type989 A) f x). Qed.
Lemma lem5430032 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f).
Proof. exact (@lem5430031 A (@IMAGE nat A) f). Qed.
Lemma lem5430033 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5430034 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term1643 A f s) = (term1644 A f s).
Proof. exact (MK_COMB (@lem5430032 A f) (@lem5430033 A s)). Qed.
Lemma lem5430036 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430037 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430036 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem5430038 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term1644 A f s) = (term1645 A f s).
Proof. exact (@lem5430037 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f) (term1599 A s)). Qed.
Lemma lem5430039 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term1643 A f s) = (term1645 A f s).
Proof. exact (TRANS (@lem5430034 A f s) (@lem5430038 A f s)). Qed.
Lemma lem5430040 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term89 A f s) = (term1645 A f s).
Proof. exact (TRANS (@lem5430028 A f s) (@lem5430039 A f s)). Qed.
Lemma lem5430041 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem5430042 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term89 A f s)) = (s = (term1645 A f s)).
Proof. exact (MK_COMB (@lem5430041 A s) (@lem5430040 A f s)). Qed.
Lemma lem5430043 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term592 A f s) = (term1646 A f s).
Proof. exact (MK_COMB (@lem5429984) (@lem5430042 A f s)). Qed.
Lemma lem5430044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430045 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5430052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430053 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430052 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430054 {A : Type'} (i'' : type661 A) (s : A -> Prop) : (i'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s).
Proof. exact (@lem5430053 A i'' s). Qed.
Lemma lem5430055 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430056 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f).
Proof. exact (MK_COMB (@lem5430054 A i'' s) (@lem5430055 A f)). Qed.
Lemma lem5430058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430059 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430058 (nat -> A) nat f x). Qed.
Lemma lem5430060 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f) = (term1647 A i'' s f).
Proof. exact (@lem5430059 A (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s) f). Qed.
Lemma lem5430062 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (term1647 A i'' s f).
Proof. exact (TRANS (@lem5430056 A i'' s f) (@lem5430060 A i'' s f)). Qed.
Lemma lem5430069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430070 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430069 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430071 {A : Type'} (j'' : type661 A) (s : A -> Prop) : (j'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s).
Proof. exact (@lem5430070 A j'' s). Qed.
Lemma lem5430072 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430073 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f).
Proof. exact (MK_COMB (@lem5430071 A j'' s) (@lem5430072 A f)). Qed.
Lemma lem5430075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430076 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430075 (nat -> A) nat f x). Qed.
Lemma lem5430077 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f) = (term1647 A j'' s f).
Proof. exact (@lem5430076 A (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s) f). Qed.
Lemma lem5430079 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (term1647 A j'' s f).
Proof. exact (TRANS (@lem5430073 A j'' s f) (@lem5430077 A j'' s f)). Qed.
Lemma lem5430080 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1648 A i'' s f) = (term1649 A i'' s f).
Proof. exact (MK_COMB (@lem5430045) (@lem5430062 A i'' s f)). Qed.
Lemma lem5430081 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : ((i'' s f) = (j'' s f)) = ((term1647 A i'' s f) = (term1647 A j'' s f)).
Proof. exact (MK_COMB (@lem5430080 A i'' s f) (@lem5430079 A j'' s f)). Qed.
Lemma lem5430082 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1650 A i'' j'' s f) = (term1651 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430044) (@lem5430081 A i'' j'' s f)). Qed.
Lemma lem5430083 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5430084 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430092 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430091 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430093 {A : Type'} (i'' : type661 A) (s : A -> Prop) : (i'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s).
Proof. exact (@lem5430092 A i'' s). Qed.
Lemma lem5430094 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430095 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f).
Proof. exact (MK_COMB (@lem5430093 A i'' s) (@lem5430094 A f)). Qed.
Lemma lem5430097 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430098 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430097 (nat -> A) nat f x). Qed.
Lemma lem5430099 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f) = (term1647 A i'' s f).
Proof. exact (@lem5430098 A (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s) f). Qed.
Lemma lem5430101 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (term1647 A i'' s f).
Proof. exact (TRANS (@lem5430095 A i'' s f) (@lem5430099 A i'' s f)). Qed.
Lemma lem5430102 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1652 A i'' s f) = (term1653 A i'' s f).
Proof. exact (MK_COMB (@lem5430084 A f) (@lem5430101 A i'' s f)). Qed.
Lemma lem5430104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430105 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430104 nat A f x). Qed.
Lemma lem5430106 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1653 A i'' s f) = (term1654 A i'' s f).
Proof. exact (@lem5430105 A f (term1647 A i'' s f)). Qed.
Lemma lem5430107 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1652 A i'' s f) = (term1654 A i'' s f).
Proof. exact (TRANS (@lem5430102 A i'' s f) (@lem5430106 A i'' s f)). Qed.
Lemma lem5430108 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430116 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430115 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430117 {A : Type'} (j'' : type661 A) (s : A -> Prop) : (j'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s).
Proof. exact (@lem5430116 A j'' s). Qed.
Lemma lem5430118 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430119 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f).
Proof. exact (MK_COMB (@lem5430117 A j'' s) (@lem5430118 A f)). Qed.
Lemma lem5430121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430122 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430121 (nat -> A) nat f x). Qed.
Lemma lem5430123 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f) = (term1647 A j'' s f).
Proof. exact (@lem5430122 A (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s) f). Qed.
Lemma lem5430125 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (term1647 A j'' s f).
Proof. exact (TRANS (@lem5430119 A j'' s f) (@lem5430123 A j'' s f)). Qed.
Lemma lem5430126 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1652 A j'' s f) = (term1653 A j'' s f).
Proof. exact (MK_COMB (@lem5430108 A f) (@lem5430125 A j'' s f)). Qed.
Lemma lem5430128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430129 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430128 nat A f x). Qed.
Lemma lem5430130 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1653 A j'' s f) = (term1654 A j'' s f).
Proof. exact (@lem5430129 A f (term1647 A j'' s f)). Qed.
Lemma lem5430131 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1652 A j'' s f) = (term1654 A j'' s f).
Proof. exact (TRANS (@lem5430126 A j'' s f) (@lem5430130 A j'' s f)). Qed.
Lemma lem5430132 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1655 A i'' s f) = (term1656 A i'' s f).
Proof. exact (MK_COMB (@lem5430083 A) (@lem5430107 A i'' s f)). Qed.
Lemma lem5430133 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : ((term1652 A i'' s f) = (term1652 A j'' s f)) = ((term1654 A i'' s f) = (term1654 A j'' s f)).
Proof. exact (MK_COMB (@lem5430132 A i'' s f) (@lem5430131 A j'' s f)). Qed.
Lemma lem5430134 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem5430141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430142 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430141 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430143 {A : Type'} (j'' : type661 A) (s : A -> Prop) : (j'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s).
Proof. exact (@lem5430142 A j'' s). Qed.
Lemma lem5430144 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430145 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f).
Proof. exact (MK_COMB (@lem5430143 A j'' s) (@lem5430144 A f)). Qed.
Lemma lem5430147 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430148 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430147 (nat -> A) nat f x). Qed.
Lemma lem5430149 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s f) = (term1647 A j'' s f).
Proof. exact (@lem5430148 A (@I ((A -> Prop) -> (nat -> A) -> nat) j'' s) f). Qed.
Lemma lem5430151 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (j'' s f) = (term1647 A j'' s f).
Proof. exact (TRANS (@lem5430145 A j'' s f) (@lem5430149 A j'' s f)). Qed.
Lemma lem5430152 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5430153 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5430158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430159 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5430158 nat nat f x). Qed.
Lemma lem5430161 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5430159 BIT1 0). Qed.
Lemma lem5430162 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5430153) (@lem5430161)). Qed.
Lemma lem5430164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430165 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5430164 nat nat f x). Qed.
Lemma lem5430166 : term1591 = term1592.
Proof. exact (@lem5430165 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5430167 : term1590 = term1592.
Proof. exact (TRANS (@lem5430162) (@lem5430166)). Qed.
Lemma lem5430172 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430173 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5430172 (A -> Prop) nat f x). Qed.
Lemma lem5430175 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5430173 A (@CARD A) s). Qed.
Lemma lem5430176 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5430152) (@lem5430167)). Qed.
Lemma lem5430177 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5430176) (@lem5430175 A s)). Qed.
Lemma lem5430179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430180 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5430179 nat type1605 f x). Qed.
Lemma lem5430181 : term1594 = term1597.
Proof. exact (@lem5430180 dotdot term1592). Qed.
Lemma lem5430182 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430183 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5430181) (@lem5430182 A s)). Qed.
Lemma lem5430185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430186 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5430185 nat (nat -> Prop) f x). Qed.
Lemma lem5430187 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5430186 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430188 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430183 A s) (@lem5430187 A s)). Qed.
Lemma lem5430189 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430177 A s) (@lem5430188 A s)). Qed.
Lemma lem5430190 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1657 A j'' s f) = (term1658 A j'' s f).
Proof. exact (MK_COMB (@lem5430134) (@lem5430151 A j'' s f)). Qed.
Lemma lem5430191 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1659 A j'' f s) = (term1660 A j'' f s).
Proof. exact (MK_COMB (@lem5430190 A j'' s f) (@lem5430189 A s)). Qed.
Lemma lem5430193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430194 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430193 nat type993 f x). Qed.
Lemma lem5430195 {A : Type'} (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1658 A j'' s f) = (term1661 A j'' s f).
Proof. exact (@lem5430194 (@IN nat) (term1647 A j'' s f)). Qed.
Lemma lem5430196 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5430197 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1660 A j'' f s) = (term1662 A j'' f s).
Proof. exact (MK_COMB (@lem5430195 A j'' s f) (@lem5430196 A s)). Qed.
Lemma lem5430199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430200 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430199 (nat -> Prop) Prop f x). Qed.
Lemma lem5430201 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1662 A j'' f s) = (term1663 A j'' f s).
Proof. exact (@lem5430200 (term1661 A j'' s f) (term1599 A s)). Qed.
Lemma lem5430202 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1660 A j'' f s) = (term1663 A j'' f s).
Proof. exact (TRANS (@lem5430197 A j'' f s) (@lem5430201 A j'' f s)). Qed.
Lemma lem5430203 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1659 A j'' f s) = (term1663 A j'' f s).
Proof. exact (TRANS (@lem5430191 A j'' f s) (@lem5430202 A j'' f s)). Qed.
Lemma lem5430204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430205 {A : Type'} (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1664 A j'' f s) = (term1665 A j'' f s).
Proof. exact (MK_COMB (@lem5430204) (@lem5430203 A j'' f s)). Qed.
Lemma lem5430206 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1666 A i'' j'' s f) = (term1667 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430205 A j'' f s) (@lem5430133 A i'' j'' s f)). Qed.
Lemma lem5430207 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem5430214 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430215 {A : Type'} (f : type661 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430214 (A -> Prop) (type977 A) f x). Qed.
Lemma lem5430216 {A : Type'} (i'' : type661 A) (s : A -> Prop) : (i'' s) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s).
Proof. exact (@lem5430215 A i'' s). Qed.
Lemma lem5430217 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430218 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f).
Proof. exact (MK_COMB (@lem5430216 A i'' s) (@lem5430217 A f)). Qed.
Lemma lem5430220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430221 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430220 (nat -> A) nat f x). Qed.
Lemma lem5430222 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s f) = (term1647 A i'' s f).
Proof. exact (@lem5430221 A (@I ((A -> Prop) -> (nat -> A) -> nat) i'' s) f). Qed.
Lemma lem5430224 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (i'' s f) = (term1647 A i'' s f).
Proof. exact (TRANS (@lem5430218 A i'' s f) (@lem5430222 A i'' s f)). Qed.
Lemma lem5430225 : dotdot = dotdot.
Proof. exact (eq_refl dotdot). Qed.
Lemma lem5430226 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem5430231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430232 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5430231 nat nat f x). Qed.
Lemma lem5430234 : (BIT1 0) = (@I (nat -> nat) BIT1 0).
Proof. exact (@lem5430232 BIT1 0). Qed.
Lemma lem5430235 : term1590 = term1591.
Proof. exact (MK_COMB (@lem5430226) (@lem5430234)). Qed.
Lemma lem5430237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430238 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5430237 nat nat f x). Qed.
Lemma lem5430239 : term1591 = term1592.
Proof. exact (@lem5430238 NUMERAL (@I (nat -> nat) BIT1 0)). Qed.
Lemma lem5430240 : term1590 = term1592.
Proof. exact (TRANS (@lem5430235) (@lem5430239)). Qed.
Lemma lem5430245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430246 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem5430245 (A -> Prop) nat f x). Qed.
Lemma lem5430248 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem5430246 A (@CARD A) s). Qed.
Lemma lem5430249 : term1593 = term1594.
Proof. exact (MK_COMB (@lem5430225) (@lem5430240)). Qed.
Lemma lem5430250 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1596 A s).
Proof. exact (MK_COMB (@lem5430249) (@lem5430248 A s)). Qed.
Lemma lem5430252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430253 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem5430252 nat type1605 f x). Qed.
Lemma lem5430254 : term1594 = term1597.
Proof. exact (@lem5430253 dotdot term1592). Qed.
Lemma lem5430255 {A : Type'} (s : A -> Prop) : (@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (eq_refl (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430256 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1598 A s).
Proof. exact (MK_COMB (@lem5430254) (@lem5430255 A s)). Qed.
Lemma lem5430258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430259 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5430258 nat (nat -> Prop) f x). Qed.
Lemma lem5430260 {A : Type'} (s : A -> Prop) : (term1598 A s) = (term1599 A s).
Proof. exact (@lem5430259 term1597 (@I ((A -> Prop) -> nat) (@CARD A) s)). Qed.
Lemma lem5430261 {A : Type'} (s : A -> Prop) : (term1596 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430256 A s) (@lem5430260 A s)). Qed.
Lemma lem5430262 {A : Type'} (s : A -> Prop) : (term1595 A s) = (term1599 A s).
Proof. exact (TRANS (@lem5430250 A s) (@lem5430261 A s)). Qed.
Lemma lem5430263 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1657 A i'' s f) = (term1658 A i'' s f).
Proof. exact (MK_COMB (@lem5430207) (@lem5430224 A i'' s f)). Qed.
Lemma lem5430264 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1659 A i'' f s) = (term1660 A i'' f s).
Proof. exact (MK_COMB (@lem5430263 A i'' s f) (@lem5430262 A s)). Qed.
Lemma lem5430266 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430267 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430266 nat type993 f x). Qed.
Lemma lem5430268 {A : Type'} (i'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1658 A i'' s f) = (term1661 A i'' s f).
Proof. exact (@lem5430267 (@IN nat) (term1647 A i'' s f)). Qed.
Lemma lem5430269 {A : Type'} (s : A -> Prop) : (term1599 A s) = (term1599 A s).
Proof. exact (eq_refl (term1599 A s)). Qed.
Lemma lem5430270 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1660 A i'' f s) = (term1662 A i'' f s).
Proof. exact (MK_COMB (@lem5430268 A i'' s f) (@lem5430269 A s)). Qed.
Lemma lem5430272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430273 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430272 (nat -> Prop) Prop f x). Qed.
Lemma lem5430274 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1662 A i'' f s) = (term1663 A i'' f s).
Proof. exact (@lem5430273 (term1661 A i'' s f) (term1599 A s)). Qed.
Lemma lem5430275 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1660 A i'' f s) = (term1663 A i'' f s).
Proof. exact (TRANS (@lem5430270 A i'' f s) (@lem5430274 A i'' f s)). Qed.
Lemma lem5430276 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1659 A i'' f s) = (term1663 A i'' f s).
Proof. exact (TRANS (@lem5430264 A i'' f s) (@lem5430275 A i'' f s)). Qed.
Lemma lem5430277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430278 {A : Type'} (i'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1664 A i'' f s) = (term1665 A i'' f s).
Proof. exact (MK_COMB (@lem5430277) (@lem5430276 A i'' f s)). Qed.
Lemma lem5430279 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1668 A i'' j'' s f) = (term1669 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430278 A i'' f s) (@lem5430206 A i'' j'' s f)). Qed.
Lemma lem5430280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430281 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1670 A i'' j'' s f) = (term1671 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430280) (@lem5430279 A i'' j'' s f)). Qed.
Lemma lem5430282 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1672 A i'' j'' s f) = (term1673 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430281 A i'' j'' s f) (@lem5430082 A i'' j'' s f)). Qed.
Lemma lem5430283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430284 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) (f : nat -> A) : (term1674 A i'' j'' s f) = (term1675 A i'' j'' s f).
Proof. exact (MK_COMB (@lem5430283) (@lem5430282 A i'' j'' s f)). Qed.
Lemma lem5430285 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f : nat -> A) (s : A -> Prop) : (term1676 A i'' j'' f s) = (term1677 A i'' j'' f s).
Proof. exact (MK_COMB (@lem5430284 A i'' j'' s f) (@lem5430043 A f s)). Qed.
Lemma lem5430286 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) : (term1678 A i'' j'' s) = (term1679 A i'' j'' s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5430285 A i'' j'' f s)). Qed.
Lemma lem5430287 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5430288 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) : (term1680 A i'' j'' s) = (term1681 A i'' j'' s).
Proof. exact (MK_COMB (@lem5430287 A) (@lem5430286 A i'' j'' s)). Qed.
Lemma lem5430293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430294 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5430293 (A -> Prop) Prop f x). Qed.
Lemma lem5430296 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5430294 A (@FINITE A) s). Qed.
Lemma lem5430297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430298 {A : Type'} (s : A -> Prop) : (term612 A s) = (term1682 A s).
Proof. exact (MK_COMB (@lem5430297) (@lem5430296 A s)). Qed.
Lemma lem5430299 {A : Type'} (i'' : type661 A) (j'' : type661 A) (s : A -> Prop) : (term794 A i'' j'' s) = (term1683 A i'' j'' s).
Proof. exact (MK_COMB (@lem5430298 A s) (@lem5430288 A i'' j'' s)). Qed.
Lemma lem5430300 {A : Type'} (i'' : type661 A) (j'' : type661 A) : (term796 A i'' j'') = (term1684 A i'' j'').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5430299 A i'' j'' s)). Qed.
Lemma lem5430301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5430302 {A : Type'} (i'' : type661 A) (j'' : type661 A) : (term798 A i'' j'') = (term1685 A i'' j'').
Proof. exact (MK_COMB (@lem5430301 A) (@lem5430300 A i'' j'')). Qed.
Lemma lem5430303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430304 {A : Type'} (i'' : type661 A) (j'' : type661 A) : (term871 A i'' j'') = (term1686 A i'' j'').
Proof. exact (MK_COMB (@lem5430303) (@lem5430302 A i'' j'')). Qed.
Lemma lem5430305 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) : (term887 A i'' j'' f'') = (term1687 A i'' j'' f'').
Proof. exact (MK_COMB (@lem5430304 A i'' j'') (@lem5429983 A f'')). Qed.
Lemma lem5430306 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1687 A i'' j'' f''.
Proof. exact (EQ_MP (@lem5430305 A i'' j'' f'') (@lem5428140 A i'' j'' f'' h1)). Qed.
Lemma lem5430315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430316 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430315 (nat -> A) (type989 A) f x). Qed.
Lemma lem5430317 {A : Type'} (f''' : nat -> A) : (@IMAGE nat A f''') = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f''').
Proof. exact (@lem5430316 A (@IMAGE nat A) f'''). Qed.
Lemma lem5430318 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430319 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (@IMAGE nat A f''' k) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f''' k).
Proof. exact (MK_COMB (@lem5430317 A f''') (@lem5430318 k)). Qed.
Lemma lem5430321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430322 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430321 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem5430323 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f''' k) = (term1573 A f''' k).
Proof. exact (@lem5430322 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f''') k). Qed.
Lemma lem5430325 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (@IMAGE nat A f''' k) = (term1573 A f''' k).
Proof. exact (TRANS (@lem5430319 A f''' k) (@lem5430323 A f''' k)). Qed.
Lemma lem5430326 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem5430327 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : (s = (@IMAGE nat A f''' k)) = (s = (term1573 A f''' k)).
Proof. exact (MK_COMB (@lem5430326 A s) (@lem5430325 A f''' k)). Qed.
Lemma lem5430332 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430333 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430332 (nat -> Prop) Prop f x). Qed.
Lemma lem5430335 (k : nat -> Prop) : (@FINITE nat k) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) k).
Proof. exact (@lem5430333 (@FINITE nat) k). Qed.
Lemma lem5430336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430337 (k : nat -> Prop) : (term1688 k) = (term1689 k).
Proof. exact (MK_COMB (@lem5430336) (@lem5430335 k)). Qed.
Lemma lem5430338 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : (term138 A s f''' k) = (term1690 A s f''' k).
Proof. exact (MK_COMB (@lem5430337 k) (@lem5430327 A s f''' k)). Qed.
Lemma lem5430343 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5430344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430345 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5430350 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430351 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430350 nat A f x). Qed.
Lemma lem5430353 {A : Type'} (f''' : nat -> A) (i : nat) : (f''' i) = (@I (nat -> A) f''' i).
Proof. exact (@lem5430351 A f''' i). Qed.
Lemma lem5430358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430359 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430358 nat A f x). Qed.
Lemma lem5430361 {A : Type'} (f''' : nat -> A) (j : nat) : (f''' j) = (@I (nat -> A) f''' j).
Proof. exact (@lem5430359 A f''' j). Qed.
Lemma lem5430362 {A : Type'} (f''' : nat -> A) (i : nat) : (term1691 A f''' i) = (term1692 A f''' i).
Proof. exact (MK_COMB (@lem5430345 A) (@lem5430353 A f''' i)). Qed.
Lemma lem5430363 {A : Type'} (i : nat) (f''' : nat -> A) (j : nat) : ((f''' i) = (f''' j)) = ((@I (nat -> A) f''' i) = (@I (nat -> A) f''' j)).
Proof. exact (MK_COMB (@lem5430362 A f''' i) (@lem5430361 A f''' j)). Qed.
Lemma lem5430364 {A : Type'} (i : nat) (f''' : nat -> A) (j : nat) : (term1693 A i f''' j) = (term1694 A i f''' j).
Proof. exact (MK_COMB (@lem5430344) (@lem5430363 A i f''' j)). Qed.
Lemma lem5430365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430372 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430373 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430372 nat type993 f x). Qed.
Lemma lem5430374 (j : nat) : (@IN nat j) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j).
Proof. exact (@lem5430373 (@IN nat) j). Qed.
Lemma lem5430375 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430376 (j : nat) (k : nat -> Prop) : (@IN nat j k) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j k).
Proof. exact (MK_COMB (@lem5430374 j) (@lem5430375 k)). Qed.
Lemma lem5430378 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430379 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430378 (nat -> Prop) Prop f x). Qed.
Lemma lem5430380 (j : nat) (k : nat -> Prop) : (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j k) = (term1695 j k).
Proof. exact (@lem5430379 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) j) k). Qed.
Lemma lem5430382 (j : nat) (k : nat -> Prop) : (@IN nat j k) = (term1695 j k).
Proof. exact (TRANS (@lem5430376 j k) (@lem5430380 j k)). Qed.
Lemma lem5430383 (j : nat) (k : nat -> Prop) : (term1696 j k) = (term1697 j k).
Proof. exact (MK_COMB (@lem5430365) (@lem5430382 j k)). Qed.
Lemma lem5430384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430385 (j : nat) (k : nat -> Prop) : (term153 j k) = (term1698 j k).
Proof. exact (MK_COMB (@lem5430384) (@lem5430383 j k)). Qed.
Lemma lem5430386 {A : Type'} (k : nat -> Prop) (i : nat) (f''' : nat -> A) (j : nat) : (term152 A k i f''' j) = (term1699 A k i f''' j).
Proof. exact (MK_COMB (@lem5430385 j k) (@lem5430364 A i f''' j)). Qed.
Lemma lem5430387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430394 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430395 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430394 nat type993 f x). Qed.
Lemma lem5430396 (i : nat) : (@IN nat i) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i).
Proof. exact (@lem5430395 (@IN nat) i). Qed.
Lemma lem5430397 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430398 (i : nat) (k : nat -> Prop) : (@IN nat i k) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i k).
Proof. exact (MK_COMB (@lem5430396 i) (@lem5430397 k)). Qed.
Lemma lem5430400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430401 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430400 (nat -> Prop) Prop f x). Qed.
Lemma lem5430402 (i : nat) (k : nat -> Prop) : (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i k) = (term1695 i k).
Proof. exact (@lem5430401 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) i) k). Qed.
Lemma lem5430404 (i : nat) (k : nat -> Prop) : (@IN nat i k) = (term1695 i k).
Proof. exact (TRANS (@lem5430398 i k) (@lem5430402 i k)). Qed.
Lemma lem5430405 (i : nat) (k : nat -> Prop) : (term1696 i k) = (term1697 i k).
Proof. exact (MK_COMB (@lem5430387) (@lem5430404 i k)). Qed.
Lemma lem5430406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430407 (i : nat) (k : nat -> Prop) : (term153 i k) = (term1698 i k).
Proof. exact (MK_COMB (@lem5430406) (@lem5430405 i k)). Qed.
Lemma lem5430408 {A : Type'} (k : nat -> Prop) (i : nat) (f''' : nat -> A) (j : nat) : (term155 A k i f''' j) = (term1700 A k i f''' j).
Proof. exact (MK_COMB (@lem5430407 i k) (@lem5430386 A k i f''' j)). Qed.
Lemma lem5430409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430410 {A : Type'} (k : nat -> Prop) (i : nat) (f''' : nat -> A) (j : nat) : (term162 A k i f''' j) = (term1701 A k i f''' j).
Proof. exact (MK_COMB (@lem5430409) (@lem5430408 A k i f''' j)). Qed.
Lemma lem5430411 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) (i : nat) (j : nat) : (term164 A k f''' i j) = (term1702 A k f''' i j).
Proof. exact (MK_COMB (@lem5430410 A k i f''' j) (@lem5430343 i j)). Qed.
Lemma lem5430412 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) (i : nat) : (term174 A k f''' i) = (term1703 A k f''' i).
Proof. exact (fun_ext (fun j : nat => @lem5430411 A k f''' i j)). Qed.
Lemma lem5430413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430414 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) (i : nat) : (term175 A k f''' i) = (term1704 A k f''' i).
Proof. exact (MK_COMB (@lem5430413) (@lem5430412 A k f''' i)). Qed.
Lemma lem5430415 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) : (term183 A k f''') = (term1705 A k f''').
Proof. exact (fun_ext (fun i : nat => @lem5430414 A k f''' i)). Qed.
Lemma lem5430416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430417 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) : (term184 A k f''') = (term1706 A k f''').
Proof. exact (MK_COMB (@lem5430416) (@lem5430415 A k f''')). Qed.
Lemma lem5430418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430419 {A : Type'} (k : nat -> Prop) (f''' : nat -> A) : (term192 A k f''') = (term1707 A k f''').
Proof. exact (MK_COMB (@lem5430418) (@lem5430417 A k f''')). Qed.
Lemma lem5430420 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : (term193 A s f''' k) = (term1708 A s f''' k).
Proof. exact (MK_COMB (@lem5430419 A k f''') (@lem5430338 A s f''' k)). Qed.
Lemma lem5430421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430427 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5430426 (A -> Prop) Prop f x). Qed.
Lemma lem5430429 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5430427 A (@FINITE A) s). Qed.
Lemma lem5430430 {A : Type'} (s : A -> Prop) : (term435 A s) = (term1638 A s).
Proof. exact (MK_COMB (@lem5430421) (@lem5430429 A s)). Qed.
Lemma lem5430431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430432 {A : Type'} (s : A -> Prop) : (term216 A s) = (term1709 A s).
Proof. exact (MK_COMB (@lem5430431) (@lem5430430 A s)). Qed.
Lemma lem5430433 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : (term456 A s f''' k) = (term1710 A s f''' k).
Proof. exact (MK_COMB (@lem5430432 A s) (@lem5430420 A s f''' k)). Qed.
Lemma lem5430434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430444 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430443 (nat -> A) (type989 A) f x). Qed.
Lemma lem5430445 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f).
Proof. exact (@lem5430444 A (@IMAGE nat A) f). Qed.
Lemma lem5430446 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430447 {A : Type'} (f : nat -> A) (k : nat -> Prop) : (@IMAGE nat A f k) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f k).
Proof. exact (MK_COMB (@lem5430445 A f) (@lem5430446 k)). Qed.
Lemma lem5430449 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430450 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5430449 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem5430451 {A : Type'} (f : nat -> A) (k : nat -> Prop) : (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f k) = (term1573 A f k).
Proof. exact (@lem5430450 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f) k). Qed.
Lemma lem5430453 {A : Type'} (f : nat -> A) (k : nat -> Prop) : (@IMAGE nat A f k) = (term1573 A f k).
Proof. exact (TRANS (@lem5430447 A f k) (@lem5430451 A f k)). Qed.
Lemma lem5430454 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem5430455 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (s = (@IMAGE nat A f k)) = (s = (term1573 A f k)).
Proof. exact (MK_COMB (@lem5430454 A s) (@lem5430453 A f k)). Qed.
Lemma lem5430456 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1711 A s f k) = (term1712 A s f k).
Proof. exact (MK_COMB (@lem5430434) (@lem5430455 A s f k)). Qed.
Lemma lem5430457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430463 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430462 (nat -> Prop) Prop f x). Qed.
Lemma lem5430465 (k : nat -> Prop) : (@FINITE nat k) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) k).
Proof. exact (@lem5430463 (@FINITE nat) k). Qed.
Lemma lem5430466 (k : nat -> Prop) : (term1486 k) = (term1576 k).
Proof. exact (MK_COMB (@lem5430457) (@lem5430465 k)). Qed.
Lemma lem5430467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430468 (k : nat -> Prop) : (term1286 k) = (term1577 k).
Proof. exact (MK_COMB (@lem5430467) (@lem5430466 k)). Qed.
Lemma lem5430469 {A : Type'} (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term186 A s f k) = (term1713 A s f k).
Proof. exact (MK_COMB (@lem5430468 k) (@lem5430456 A s f k)). Qed.
Lemma lem5430470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5430471 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5430478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430479 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430478 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430480 {A : Type'} (i''' : type984 A) (k : nat -> Prop) : (i''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k).
Proof. exact (@lem5430479 A i''' k). Qed.
Lemma lem5430481 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430482 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f).
Proof. exact (MK_COMB (@lem5430480 A i''' k) (@lem5430481 A f)). Qed.
Lemma lem5430484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430485 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430484 (nat -> A) nat f x). Qed.
Lemma lem5430486 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f) = (term1714 A i''' k f).
Proof. exact (@lem5430485 A (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k) f). Qed.
Lemma lem5430488 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (term1714 A i''' k f).
Proof. exact (TRANS (@lem5430482 A i''' k f) (@lem5430486 A i''' k f)). Qed.
Lemma lem5430495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430496 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430495 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430497 {A : Type'} (j''' : type984 A) (k : nat -> Prop) : (j''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k).
Proof. exact (@lem5430496 A j''' k). Qed.
Lemma lem5430498 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430499 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f).
Proof. exact (MK_COMB (@lem5430497 A j''' k) (@lem5430498 A f)). Qed.
Lemma lem5430501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430502 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430501 (nat -> A) nat f x). Qed.
Lemma lem5430503 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f) = (term1714 A j''' k f).
Proof. exact (@lem5430502 A (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k) f). Qed.
Lemma lem5430505 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (term1714 A j''' k f).
Proof. exact (TRANS (@lem5430499 A j''' k f) (@lem5430503 A j''' k f)). Qed.
Lemma lem5430506 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1715 A i''' k f) = (term1716 A i''' k f).
Proof. exact (MK_COMB (@lem5430471) (@lem5430488 A i''' k f)). Qed.
Lemma lem5430507 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : ((i''' k f) = (j''' k f)) = ((term1714 A i''' k f) = (term1714 A j''' k f)).
Proof. exact (MK_COMB (@lem5430506 A i''' k f) (@lem5430505 A j''' k f)). Qed.
Lemma lem5430508 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1717 A i''' j''' k f) = (term1718 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430470) (@lem5430507 A i''' j''' k f)). Qed.
Lemma lem5430509 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5430510 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430517 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430518 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430517 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430519 {A : Type'} (i''' : type984 A) (k : nat -> Prop) : (i''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k).
Proof. exact (@lem5430518 A i''' k). Qed.
Lemma lem5430520 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430521 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f).
Proof. exact (MK_COMB (@lem5430519 A i''' k) (@lem5430520 A f)). Qed.
Lemma lem5430523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430524 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430523 (nat -> A) nat f x). Qed.
Lemma lem5430525 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f) = (term1714 A i''' k f).
Proof. exact (@lem5430524 A (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k) f). Qed.
Lemma lem5430527 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (term1714 A i''' k f).
Proof. exact (TRANS (@lem5430521 A i''' k f) (@lem5430525 A i''' k f)). Qed.
Lemma lem5430528 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1719 A i''' k f) = (term1720 A i''' k f).
Proof. exact (MK_COMB (@lem5430510 A f) (@lem5430527 A i''' k f)). Qed.
Lemma lem5430530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430531 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430530 nat A f x). Qed.
Lemma lem5430532 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1720 A i''' k f) = (term1721 A i''' k f).
Proof. exact (@lem5430531 A f (term1714 A i''' k f)). Qed.
Lemma lem5430533 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1719 A i''' k f) = (term1721 A i''' k f).
Proof. exact (TRANS (@lem5430528 A i''' k f) (@lem5430532 A i''' k f)). Qed.
Lemma lem5430534 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430542 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430541 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430543 {A : Type'} (j''' : type984 A) (k : nat -> Prop) : (j''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k).
Proof. exact (@lem5430542 A j''' k). Qed.
Lemma lem5430544 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430545 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f).
Proof. exact (MK_COMB (@lem5430543 A j''' k) (@lem5430544 A f)). Qed.
Lemma lem5430547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430548 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430547 (nat -> A) nat f x). Qed.
Lemma lem5430549 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f) = (term1714 A j''' k f).
Proof. exact (@lem5430548 A (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k) f). Qed.
Lemma lem5430551 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (term1714 A j''' k f).
Proof. exact (TRANS (@lem5430545 A j''' k f) (@lem5430549 A j''' k f)). Qed.
Lemma lem5430552 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1719 A j''' k f) = (term1720 A j''' k f).
Proof. exact (MK_COMB (@lem5430534 A f) (@lem5430551 A j''' k f)). Qed.
Lemma lem5430554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430555 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5430554 nat A f x). Qed.
Lemma lem5430556 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1720 A j''' k f) = (term1721 A j''' k f).
Proof. exact (@lem5430555 A f (term1714 A j''' k f)). Qed.
Lemma lem5430557 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1719 A j''' k f) = (term1721 A j''' k f).
Proof. exact (TRANS (@lem5430552 A j''' k f) (@lem5430556 A j''' k f)). Qed.
Lemma lem5430558 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1722 A i''' k f) = (term1723 A i''' k f).
Proof. exact (MK_COMB (@lem5430509 A) (@lem5430533 A i''' k f)). Qed.
Lemma lem5430559 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : ((term1719 A i''' k f) = (term1719 A j''' k f)) = ((term1721 A i''' k f) = (term1721 A j''' k f)).
Proof. exact (MK_COMB (@lem5430558 A i''' k f) (@lem5430557 A j''' k f)). Qed.
Lemma lem5430560 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem5430567 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430568 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430567 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430569 {A : Type'} (j''' : type984 A) (k : nat -> Prop) : (j''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k).
Proof. exact (@lem5430568 A j''' k). Qed.
Lemma lem5430570 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430571 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f).
Proof. exact (MK_COMB (@lem5430569 A j''' k) (@lem5430570 A f)). Qed.
Lemma lem5430573 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430574 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430573 (nat -> A) nat f x). Qed.
Lemma lem5430575 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k f) = (term1714 A j''' k f).
Proof. exact (@lem5430574 A (@I ((nat -> Prop) -> (nat -> A) -> nat) j''' k) f). Qed.
Lemma lem5430577 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (j''' k f) = (term1714 A j''' k f).
Proof. exact (TRANS (@lem5430571 A j''' k f) (@lem5430575 A j''' k f)). Qed.
Lemma lem5430578 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430579 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1724 A j''' k f) = (term1725 A j''' k f).
Proof. exact (MK_COMB (@lem5430560) (@lem5430577 A j''' k f)). Qed.
Lemma lem5430580 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1726 A j''' f k) = (term1727 A j''' f k).
Proof. exact (MK_COMB (@lem5430579 A j''' k f) (@lem5430578 k)). Qed.
Lemma lem5430582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430583 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430582 nat type993 f x). Qed.
Lemma lem5430584 {A : Type'} (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1725 A j''' k f) = (term1728 A j''' k f).
Proof. exact (@lem5430583 (@IN nat) (term1714 A j''' k f)). Qed.
Lemma lem5430585 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430586 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1727 A j''' f k) = (term1729 A j''' f k).
Proof. exact (MK_COMB (@lem5430584 A j''' k f) (@lem5430585 k)). Qed.
Lemma lem5430588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430589 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430588 (nat -> Prop) Prop f x). Qed.
Lemma lem5430590 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1729 A j''' f k) = (term1730 A j''' f k).
Proof. exact (@lem5430589 (term1728 A j''' k f) k). Qed.
Lemma lem5430591 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1727 A j''' f k) = (term1730 A j''' f k).
Proof. exact (TRANS (@lem5430586 A j''' f k) (@lem5430590 A j''' f k)). Qed.
Lemma lem5430592 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1726 A j''' f k) = (term1730 A j''' f k).
Proof. exact (TRANS (@lem5430580 A j''' f k) (@lem5430591 A j''' f k)). Qed.
Lemma lem5430593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430594 {A : Type'} (j''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1731 A j''' f k) = (term1732 A j''' f k).
Proof. exact (MK_COMB (@lem5430593) (@lem5430592 A j''' f k)). Qed.
Lemma lem5430595 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1733 A i''' j''' k f) = (term1734 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430594 A j''' f k) (@lem5430559 A i''' j''' k f)). Qed.
Lemma lem5430596 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem5430603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430604 {A : Type'} (f : type984 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> A) -> nat) f x).
Proof. exact (@lem5430603 (nat -> Prop) (type977 A) f x). Qed.
Lemma lem5430605 {A : Type'} (i''' : type984 A) (k : nat -> Prop) : (i''' k) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k).
Proof. exact (@lem5430604 A i''' k). Qed.
Lemma lem5430606 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5430607 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f).
Proof. exact (MK_COMB (@lem5430605 A i''' k) (@lem5430606 A f)). Qed.
Lemma lem5430609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430610 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem5430609 (nat -> A) nat f x). Qed.
Lemma lem5430611 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k f) = (term1714 A i''' k f).
Proof. exact (@lem5430610 A (@I ((nat -> Prop) -> (nat -> A) -> nat) i''' k) f). Qed.
Lemma lem5430613 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (i''' k f) = (term1714 A i''' k f).
Proof. exact (TRANS (@lem5430607 A i''' k f) (@lem5430611 A i''' k f)). Qed.
Lemma lem5430614 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430615 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1724 A i''' k f) = (term1725 A i''' k f).
Proof. exact (MK_COMB (@lem5430596) (@lem5430613 A i''' k f)). Qed.
Lemma lem5430616 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1726 A i''' f k) = (term1727 A i''' f k).
Proof. exact (MK_COMB (@lem5430615 A i''' k f) (@lem5430614 k)). Qed.
Lemma lem5430618 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430619 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430618 nat type993 f x). Qed.
Lemma lem5430620 {A : Type'} (i''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1725 A i''' k f) = (term1728 A i''' k f).
Proof. exact (@lem5430619 (@IN nat) (term1714 A i''' k f)). Qed.
Lemma lem5430621 (k : nat -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem5430622 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1727 A i''' f k) = (term1729 A i''' f k).
Proof. exact (MK_COMB (@lem5430620 A i''' k f) (@lem5430621 k)). Qed.
Lemma lem5430624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430625 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem5430624 (nat -> Prop) Prop f x). Qed.
Lemma lem5430626 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1729 A i''' f k) = (term1730 A i''' f k).
Proof. exact (@lem5430625 (term1728 A i''' k f) k). Qed.
Lemma lem5430627 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1727 A i''' f k) = (term1730 A i''' f k).
Proof. exact (TRANS (@lem5430622 A i''' f k) (@lem5430626 A i''' f k)). Qed.
Lemma lem5430628 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1726 A i''' f k) = (term1730 A i''' f k).
Proof. exact (TRANS (@lem5430616 A i''' f k) (@lem5430627 A i''' f k)). Qed.
Lemma lem5430629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430630 {A : Type'} (i''' : type984 A) (f : nat -> A) (k : nat -> Prop) : (term1731 A i''' f k) = (term1732 A i''' f k).
Proof. exact (MK_COMB (@lem5430629) (@lem5430628 A i''' f k)). Qed.
Lemma lem5430631 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1735 A i''' j''' k f) = (term1736 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430630 A i''' f k) (@lem5430595 A i''' j''' k f)). Qed.
Lemma lem5430632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430633 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1737 A i''' j''' k f) = (term1738 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430632) (@lem5430631 A i''' j''' k f)). Qed.
Lemma lem5430634 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1739 A i''' j''' k f) = (term1740 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430633 A i''' j''' k f) (@lem5430508 A i''' j''' k f)). Qed.
Lemma lem5430635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430636 {A : Type'} (i''' : type984 A) (j''' : type984 A) (k : nat -> Prop) (f : nat -> A) : (term1741 A i''' j''' k f) = (term1742 A i''' j''' k f).
Proof. exact (MK_COMB (@lem5430635) (@lem5430634 A i''' j''' k f)). Qed.
Lemma lem5430637 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1743 A i''' j''' s f k) = (term1744 A i''' j''' s f k).
Proof. exact (MK_COMB (@lem5430636 A i''' j''' k f) (@lem5430469 A s f k)). Qed.
Lemma lem5430638 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term1745 A i''' j''' s k) = (term1746 A i''' j''' s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5430637 A i''' j''' s f k)). Qed.
Lemma lem5430639 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5430640 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term387 A i''' j''' s k) = (term1747 A i''' j''' s k).
Proof. exact (MK_COMB (@lem5430639 A) (@lem5430638 A i''' j''' s k)). Qed.
Lemma lem5430641 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term389 A i''' j''' s) = (term1748 A i''' j''' s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5430640 A i''' j''' s k)). Qed.
Lemma lem5430642 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5430643 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term391 A i''' j''' s) = (term1749 A i''' j''' s).
Proof. exact (MK_COMB (@lem5430642) (@lem5430641 A i''' j''' s)). Qed.
Lemma lem5430648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5430649 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5430648 (A -> Prop) Prop f x). Qed.
Lemma lem5430651 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5430649 A (@FINITE A) s). Qed.
Lemma lem5430652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430653 {A : Type'} (s : A -> Prop) : (term219 A s) = (term1750 A s).
Proof. exact (MK_COMB (@lem5430652) (@lem5430651 A s)). Qed.
Lemma lem5430654 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term422 A i''' j''' s) = (term1751 A i''' j''' s).
Proof. exact (MK_COMB (@lem5430653 A s) (@lem5430643 A i''' j''' s)). Qed.
Lemma lem5430655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5430656 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term509 A i''' j''' s) = (term1752 A i''' j''' s).
Proof. exact (MK_COMB (@lem5430655) (@lem5430654 A i''' j''' s)). Qed.
Lemma lem5430657 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : (term541 A i''' j''' s f''' k) = (term1753 A i''' j''' s f''' k).
Proof. exact (MK_COMB (@lem5430656 A i''' j''' s) (@lem5430433 A s f''' k)). Qed.
Lemma lem5430658 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term541 A i''' j''' s f''' k) : term1753 A i''' j''' s f''' k.
Proof. exact (EQ_MP (@lem5430657 A i''' j''' s f''' k) (@lem5428145 A i''' j''' s f''' k h1)). Qed.
Lemma lem5430659 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1642 A f''.
Proof. exact (proj2 (@lem5430306 A i'' j'' f'' h1)). Qed.
Lemma lem5430665 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1751 A i''' j''' s.
Proof. exact (h1). Qed.
Lemma lem5430666 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1710 A s f''' k.
Proof. exact (h1). Qed.
Lemma lem5430667 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1749 A i''' j''' s.
Proof. exact (proj2 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5430669 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1708 A s f''' k.
Proof. exact (proj2 (@lem5430666 A s f''' k h1)). Qed.
Lemma lem5430671 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1690 A s f''' k.
Proof. exact (proj2 (@lem5430669 A s f''' k h1)). Qed.
Lemma lem5430820 (m : nat) (n : nat) : (term1585 m n) = (term1585 m n).
Proof. exact (eq_refl (term1585 m n)). Qed.
Lemma lem5430821 (m : nat) : (term1586 m) = (term1586 m).
Proof. exact (fun_ext (fun n : nat => @lem5430820 m n)). Qed.
Lemma lem5430822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430823 (m : nat) : (term1587 m) = (term1587 m).
Proof. exact (MK_COMB (@lem5430822) (@lem5430821 m)). Qed.
Lemma lem5430824 : term1588 = term1588.
Proof. exact (fun_ext (fun m : nat => @lem5430823 m)). Qed.
Lemma lem5430825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430827 : term1589 = term1589.
Proof. exact (MK_COMB (@lem5430825) (@lem5430824)). Qed.
Lemma lem5430828 (h1 : term105) : term1589.
Proof. exact (EQ_MP (@lem5430827) (@lem5428572 h1)). Qed.
Lemma lem5430922 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1754 A P Q) = (term1755 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5430923 (P : nat -> Prop) (Q : Prop) : (term1756 P Q) = (term1757 P Q).
Proof. exact (@lem5430922 nat P Q). Qed.
Lemma lem5430924 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1758 A f'' s) = (term1759 A f'' s).
Proof. exact (@lem5430923 (term1631 A f'' s) (s = (term1606 A f'' s))). Qed.
Lemma lem5430925 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1760 A f'' s i) = (term1629 A f'' s i).
Proof. exact (eq_refl (term1760 A f'' s i)). Qed.
Lemma lem5430926 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1761 A f'' s) = (term1631 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5430925 A f'' s i)). Qed.
Lemma lem5430927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430928 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1762 A f'' s) = (term1633 A f'' s).
Proof. exact (MK_COMB (@lem5430927) (@lem5430926 A f'' s)). Qed.
Lemma lem5430929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430930 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1763 A f'' s) = (term1635 A f'' s).
Proof. exact (MK_COMB (@lem5430929) (@lem5430928 A f'' s)). Qed.
Lemma lem5430931 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (s = (term1606 A f'' s)) = (s = (term1606 A f'' s)).
Proof. exact (eq_refl (s = (term1606 A f'' s))). Qed.
Lemma lem5430932 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1758 A f'' s) = (term1637 A f'' s).
Proof. exact (MK_COMB (@lem5430930 A f'' s) (@lem5430931 A f'' s)). Qed.
Lemma lem5430933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5430934 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1764 A f'' s) = (term1765 A f'' s).
Proof. exact (MK_COMB (@lem5430933) (@lem5430932 A f'' s)). Qed.
Lemma lem5430935 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1760 A f'' s i) = (term1629 A f'' s i).
Proof. exact (eq_refl (term1760 A f'' s i)). Qed.
Lemma lem5430936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430937 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1766 A f'' s i) = (term1767 A f'' s i).
Proof. exact (MK_COMB (@lem5430936) (@lem5430935 A f'' s i)). Qed.
Lemma lem5430938 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (s = (term1606 A f'' s)) = (s = (term1606 A f'' s)).
Proof. exact (eq_refl (s = (term1606 A f'' s))). Qed.
Lemma lem5430939 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1768 A i f'' s) = (term1769 A i f'' s).
Proof. exact (MK_COMB (@lem5430937 A f'' s i) (@lem5430938 A f'' s)). Qed.
Lemma lem5430940 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1770 A f'' s) = (term1771 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5430939 A i f'' s)). Qed.
Lemma lem5430941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430942 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1759 A f'' s) = (term1772 A f'' s).
Proof. exact (MK_COMB (@lem5430941) (@lem5430940 A f'' s)). Qed.
Lemma lem5430943 {A : Type'} (f'' : type681 A) (s : A -> Prop) : ((term1758 A f'' s) = (term1759 A f'' s)) = ((term1637 A f'' s) = (term1772 A f'' s)).
Proof. exact (MK_COMB (@lem5430934 A f'' s) (@lem5430942 A f'' s)). Qed.
Lemma lem5430944 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1637 A f'' s) = (term1772 A f'' s).
Proof. exact (EQ_MP (@lem5430943 A f'' s) (@lem5430924 A f'' s)). Qed.
Lemma lem5430946 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1754 A P Q) = (term1755 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5430947 (P : nat -> Prop) (Q : Prop) : (term1756 P Q) = (term1757 P Q).
Proof. exact (@lem5430946 nat P Q). Qed.
Lemma lem5430948 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1773 A i f'' s) = (term1774 A i f'' s).
Proof. exact (@lem5430947 (term1627 A f'' s i) (s = (term1606 A f'' s))). Qed.
Lemma lem5430949 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) (j : nat) : (term1775 A f'' s i j) = (term1625 A f'' s i j).
Proof. exact (eq_refl (term1775 A f'' s i j)). Qed.
Lemma lem5430950 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1776 A f'' s i) = (term1627 A f'' s i).
Proof. exact (fun_ext (fun j : nat => @lem5430949 A f'' s i j)). Qed.
Lemma lem5430951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430952 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1777 A f'' s i) = (term1629 A f'' s i).
Proof. exact (MK_COMB (@lem5430951) (@lem5430950 A f'' s i)). Qed.
Lemma lem5430953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430954 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) : (term1778 A f'' s i) = (term1767 A f'' s i).
Proof. exact (MK_COMB (@lem5430953) (@lem5430952 A f'' s i)). Qed.
Lemma lem5430955 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (s = (term1606 A f'' s)) = (s = (term1606 A f'' s)).
Proof. exact (eq_refl (s = (term1606 A f'' s))). Qed.
Lemma lem5430956 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1773 A i f'' s) = (term1769 A i f'' s).
Proof. exact (MK_COMB (@lem5430954 A f'' s i) (@lem5430955 A f'' s)). Qed.
Lemma lem5430957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5430958 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1779 A i f'' s) = (term1780 A i f'' s).
Proof. exact (MK_COMB (@lem5430957) (@lem5430956 A i f'' s)). Qed.
Lemma lem5430959 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) (j : nat) : (term1775 A f'' s i j) = (term1625 A f'' s i j).
Proof. exact (eq_refl (term1775 A f'' s i j)). Qed.
Lemma lem5430960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5430961 {A : Type'} (f'' : type681 A) (s : A -> Prop) (i : nat) (j : nat) : (term1781 A f'' s i j) = (term1782 A f'' s i j).
Proof. exact (MK_COMB (@lem5430960) (@lem5430959 A f'' s i j)). Qed.
Lemma lem5430962 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (s = (term1606 A f'' s)) = (s = (term1606 A f'' s)).
Proof. exact (eq_refl (s = (term1606 A f'' s))). Qed.
Lemma lem5430963 {A : Type'} (i : nat) (j : nat) (f'' : type681 A) (s : A -> Prop) : (term1783 A i j f'' s) = (term1784 A i j f'' s).
Proof. exact (MK_COMB (@lem5430961 A f'' s i j) (@lem5430962 A f'' s)). Qed.
Lemma lem5430964 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1785 A i f'' s) = (term1786 A i f'' s).
Proof. exact (fun_ext (fun j : nat => @lem5430963 A i j f'' s)). Qed.
Lemma lem5430965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430966 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1774 A i f'' s) = (term1787 A i f'' s).
Proof. exact (MK_COMB (@lem5430965) (@lem5430964 A i f'' s)). Qed.
Lemma lem5430967 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : ((term1773 A i f'' s) = (term1774 A i f'' s)) = ((term1769 A i f'' s) = (term1787 A i f'' s)).
Proof. exact (MK_COMB (@lem5430958 A i f'' s) (@lem5430966 A i f'' s)). Qed.
Lemma lem5430968 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1769 A i f'' s) = (term1787 A i f'' s).
Proof. exact (EQ_MP (@lem5430967 A i f'' s) (@lem5430948 A i f'' s)). Qed.
Lemma lem5430969 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1771 A f'' s) = (term1788 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5430968 A i f'' s)). Qed.
Lemma lem5430970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430971 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1772 A f'' s) = (term1789 A f'' s).
Proof. exact (MK_COMB (@lem5430970) (@lem5430969 A f'' s)). Qed.
Lemma lem5430972 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1637 A f'' s) = (term1789 A f'' s).
Proof. exact (TRANS (@lem5430944 A f'' s) (@lem5430971 A f'' s)). Qed.
Lemma lem5430973 {A : Type'} (s : A -> Prop) : (term1639 A s) = (term1639 A s).
Proof. exact (eq_refl (term1639 A s)). Qed.
Lemma lem5430974 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1640 A f'' s) = (term1790 A f'' s).
Proof. exact (MK_COMB (@lem5430973 A s) (@lem5430972 A f'' s)). Qed.
Lemma lem5430976 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1791 A P Q) = (term1792 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5430977 (P : Prop) (Q : nat -> Prop) : (term1793 P Q) = (term1794 P Q).
Proof. exact (@lem5430976 nat P Q). Qed.
Lemma lem5430978 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1795 A f'' s) = (term1796 A f'' s).
Proof. exact (@lem5430977 (term1638 A s) (term1788 A f'' s)). Qed.
Lemma lem5430979 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1797 A f'' s i) = (term1787 A i f'' s).
Proof. exact (eq_refl (term1797 A f'' s i)). Qed.
Lemma lem5430980 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1798 A f'' s) = (term1788 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5430979 A i f'' s)). Qed.
Lemma lem5430981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430982 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1799 A f'' s) = (term1789 A f'' s).
Proof. exact (MK_COMB (@lem5430981) (@lem5430980 A f'' s)). Qed.
Lemma lem5430983 {A : Type'} (s : A -> Prop) : (term1639 A s) = (term1639 A s).
Proof. exact (eq_refl (term1639 A s)). Qed.
Lemma lem5430984 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1795 A f'' s) = (term1790 A f'' s).
Proof. exact (MK_COMB (@lem5430983 A s) (@lem5430982 A f'' s)). Qed.
Lemma lem5430985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5430986 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1800 A f'' s) = (term1801 A f'' s).
Proof. exact (MK_COMB (@lem5430985) (@lem5430984 A f'' s)). Qed.
Lemma lem5430987 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1797 A f'' s i) = (term1787 A i f'' s).
Proof. exact (eq_refl (term1797 A f'' s i)). Qed.
Lemma lem5430988 {A : Type'} (s : A -> Prop) : (term1639 A s) = (term1639 A s).
Proof. exact (eq_refl (term1639 A s)). Qed.
Lemma lem5430989 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1802 A f'' s i) = (term1803 A i f'' s).
Proof. exact (MK_COMB (@lem5430988 A s) (@lem5430987 A i f'' s)). Qed.
Lemma lem5430990 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1804 A f'' s) = (term1805 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5430989 A i f'' s)). Qed.
Lemma lem5430991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5430992 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1796 A f'' s) = (term1806 A f'' s).
Proof. exact (MK_COMB (@lem5430991) (@lem5430990 A f'' s)). Qed.
Lemma lem5430993 {A : Type'} (f'' : type681 A) (s : A -> Prop) : ((term1795 A f'' s) = (term1796 A f'' s)) = ((term1790 A f'' s) = (term1806 A f'' s)).
Proof. exact (MK_COMB (@lem5430986 A f'' s) (@lem5430992 A f'' s)). Qed.
Lemma lem5430994 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1790 A f'' s) = (term1806 A f'' s).
Proof. exact (EQ_MP (@lem5430993 A f'' s) (@lem5430978 A f'' s)). Qed.
Lemma lem5430996 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1791 A P Q) = (term1792 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5430997 (P : Prop) (Q : nat -> Prop) : (term1793 P Q) = (term1794 P Q).
Proof. exact (@lem5430996 nat P Q). Qed.
Lemma lem5430998 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1807 A i f'' s) = (term1808 A i f'' s).
Proof. exact (@lem5430997 (term1638 A s) (term1786 A i f'' s)). Qed.
Lemma lem5430999 {A : Type'} (i : nat) (j : nat) (f'' : type681 A) (s : A -> Prop) : (term1809 A i f'' s j) = (term1784 A i j f'' s).
Proof. exact (eq_refl (term1809 A i f'' s j)). Qed.
Lemma lem5431000 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1810 A i f'' s) = (term1786 A i f'' s).
Proof. exact (fun_ext (fun j : nat => @lem5430999 A i j f'' s)). Qed.
Lemma lem5431001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5431002 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1811 A i f'' s) = (term1787 A i f'' s).
Proof. exact (MK_COMB (@lem5431001) (@lem5431000 A i f'' s)). Qed.
Lemma lem5431003 {A : Type'} (s : A -> Prop) : (term1639 A s) = (term1639 A s).
Proof. exact (eq_refl (term1639 A s)). Qed.
Lemma lem5431004 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1807 A i f'' s) = (term1803 A i f'' s).
Proof. exact (MK_COMB (@lem5431003 A s) (@lem5431002 A i f'' s)). Qed.
Lemma lem5431005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5431006 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1812 A i f'' s) = (term1813 A i f'' s).
Proof. exact (MK_COMB (@lem5431005) (@lem5431004 A i f'' s)). Qed.
Lemma lem5431007 {A : Type'} (i : nat) (j : nat) (f'' : type681 A) (s : A -> Prop) : (term1809 A i f'' s j) = (term1784 A i j f'' s).
Proof. exact (eq_refl (term1809 A i f'' s j)). Qed.
Lemma lem5431008 {A : Type'} (s : A -> Prop) : (term1639 A s) = (term1639 A s).
Proof. exact (eq_refl (term1639 A s)). Qed.
Lemma lem5431009 {A : Type'} (i : nat) (j : nat) (f'' : type681 A) (s : A -> Prop) : (term1814 A i f'' s j) = (term1815 A i j f'' s).
Proof. exact (MK_COMB (@lem5431008 A s) (@lem5431007 A i j f'' s)). Qed.
Lemma lem5431010 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1816 A i f'' s) = (term1817 A i f'' s).
Proof. exact (fun_ext (fun j : nat => @lem5431009 A i j f'' s)). Qed.
Lemma lem5431011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5431012 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1808 A i f'' s) = (term1818 A i f'' s).
Proof. exact (MK_COMB (@lem5431011) (@lem5431010 A i f'' s)). Qed.
Lemma lem5431013 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : ((term1807 A i f'' s) = (term1808 A i f'' s)) = ((term1803 A i f'' s) = (term1818 A i f'' s)).
Proof. exact (MK_COMB (@lem5431006 A i f'' s) (@lem5431012 A i f'' s)). Qed.
Lemma lem5431014 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1803 A i f'' s) = (term1818 A i f'' s).
Proof. exact (EQ_MP (@lem5431013 A i f'' s) (@lem5430998 A i f'' s)). Qed.
Lemma lem5431015 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1805 A f'' s) = (term1819 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5431014 A i f'' s)). Qed.
Lemma lem5431016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5431017 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1806 A f'' s) = (term1820 A f'' s).
Proof. exact (MK_COMB (@lem5431016) (@lem5431015 A f'' s)). Qed.
Lemma lem5431018 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1790 A f'' s) = (term1820 A f'' s).
Proof. exact (TRANS (@lem5430994 A f'' s) (@lem5431017 A f'' s)). Qed.
Lemma lem5431019 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1640 A f'' s) = (term1820 A f'' s).
Proof. exact (TRANS (@lem5430974 A f'' s) (@lem5431018 A f'' s)). Qed.
Lemma lem5431020 {A : Type'} (f'' : type681 A) : (term1641 A f'') = (term1821 A f'').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5431019 A f'' s)). Qed.
Lemma lem5431021 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5431022 {A : Type'} (f'' : type681 A) : (term1642 A f'') = (term1822 A f'').
Proof. exact (MK_COMB (@lem5431021 A) (@lem5431020 A f'')). Qed.
Lemma lem5431057 {A : Type'} (i : nat) (j : nat) (f'' : type681 A) (s : A -> Prop) : (term1815 A i j f'' s) = (term1823 A i j f'' s).
Proof. exact (@lem19490 (term1625 A f'' s i j) (term1638 A s) (s = (term1606 A f'' s))). Qed.
Lemma lem5431058 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1817 A i f'' s) = (term1824 A i f'' s).
Proof. exact (fun_ext (fun j : nat => @lem5431057 A i j f'' s)). Qed.
Lemma lem5431059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5431060 {A : Type'} (i : nat) (f'' : type681 A) (s : A -> Prop) : (term1818 A i f'' s) = (term1825 A i f'' s).
Proof. exact (MK_COMB (@lem5431059) (@lem5431058 A i f'' s)). Qed.
Lemma lem5431061 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1819 A f'' s) = (term1826 A f'' s).
Proof. exact (fun_ext (fun i : nat => @lem5431060 A i f'' s)). Qed.
Lemma lem5431062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5431063 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1820 A f'' s) = (term1827 A f'' s).
Proof. exact (MK_COMB (@lem5431062) (@lem5431061 A f'' s)). Qed.
Lemma lem5431064 {A : Type'} (f'' : type681 A) : (term1821 A f'') = (term1828 A f'').
Proof. exact (fun_ext (fun s : A -> Prop => @lem5431063 A f'' s)). Qed.
Lemma lem5431065 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5431066 {A : Type'} (f'' : type681 A) : (term1822 A f'') = (term1829 A f'').
Proof. exact (MK_COMB (@lem5431065 A) (@lem5431064 A f'')). Qed.
Lemma lem5431067 {A : Type'} (f'' : type681 A) : (term1642 A f'') = (term1829 A f'').
Proof. exact (TRANS (@lem5431022 A f'') (@lem5431066 A f'')). Qed.
Lemma lem5431068 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1829 A f''.
Proof. exact (EQ_MP (@lem5431067 A f'') (@lem5430659 A i'' j'' f'' h1)). Qed.
Lemma lem5431577 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1744 A i''' j''' s f k) = (term1830 A i''' j''' s f k).
Proof. exact (@lem19699 (term1736 A i''' j''' k f) (term1718 A i''' j''' k f) (term1713 A s f k)). Qed.
Lemma lem5431578 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1831 A i''' j''' s f k) = (term1831 A i''' j''' s f k).
Proof. exact (eq_refl (term1831 A i''' j''' s f k)). Qed.
Lemma lem5431579 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1832 A i''' j''' s f k) = (term1833 A i''' j''' s f k).
Proof. exact (@lem19699 (term1730 A i''' f k) (term1734 A i''' j''' k f) (term1713 A s f k)). Qed.
Lemma lem5431586 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1834 A i''' j''' s f k) = (term1835 A i''' j''' s f k).
Proof. exact (@lem19699 (term1730 A j''' f k) ((term1721 A i''' k f) = (term1721 A j''' k f)) (term1713 A s f k)). Qed.
Lemma lem5431589 {A : Type'} (i''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1836 A i''' s f k) = (term1836 A i''' s f k).
Proof. exact (eq_refl (term1836 A i''' s f k)). Qed.
Lemma lem5431590 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1833 A i''' j''' s f k) = (term1837 A i''' j''' s f k).
Proof. exact (MK_COMB (@lem5431589 A i''' s f k) (@lem5431586 A i''' j''' s f k)). Qed.
Lemma lem5431591 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1832 A i''' j''' s f k) = (term1837 A i''' j''' s f k).
Proof. exact (TRANS (@lem5431579 A i''' j''' s f k) (@lem5431590 A i''' j''' s f k)). Qed.
Lemma lem5431592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5431593 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1838 A i''' j''' s f k) = (term1839 A i''' j''' s f k).
Proof. exact (MK_COMB (@lem5431592) (@lem5431591 A i''' j''' s f k)). Qed.
Lemma lem5431594 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1830 A i''' j''' s f k) = (term1840 A i''' j''' s f k).
Proof. exact (MK_COMB (@lem5431593 A i''' j''' s f k) (@lem5431578 A i''' j''' s f k)). Qed.
Lemma lem5431596 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f : nat -> A) (k : nat -> Prop) : (term1744 A i''' j''' s f k) = (term1840 A i''' j''' s f k).
Proof. exact (TRANS (@lem5431577 A i''' j''' s f k) (@lem5431594 A i''' j''' s f k)). Qed.
Lemma lem5431597 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term1746 A i''' j''' s k) = (term1841 A i''' j''' s k).
Proof. exact (fun_ext (fun f : nat -> A => @lem5431596 A i''' j''' s f k)). Qed.
Lemma lem5431598 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5431599 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) : (term1747 A i''' j''' s k) = (term1842 A i''' j''' s k).
Proof. exact (MK_COMB (@lem5431598 A) (@lem5431597 A i''' j''' s k)). Qed.
Lemma lem5431600 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term1748 A i''' j''' s) = (term1843 A i''' j''' s).
Proof. exact (fun_ext (fun k : nat -> Prop => @lem5431599 A i''' j''' s k)). Qed.
Lemma lem5431601 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5431603 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) : (term1749 A i''' j''' s) = (term1844 A i''' j''' s).
Proof. exact (MK_COMB (@lem5431601) (@lem5431600 A i''' j''' s)). Qed.
Lemma lem5431604 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1844 A i''' j''' s.
Proof. exact (EQ_MP (@lem5431603 A i''' j''' s) (@lem5430667 A i''' j''' s h1)). Qed.
Lemma lem5431692 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1578 A f s) = (term1578 A f s).
Proof. exact (eq_refl (term1578 A f s)). Qed.
Lemma lem5431693 {A : Type'} (f : nat -> A) : (term1579 A f) = (term1579 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5431692 A f s)). Qed.
Lemma lem5431694 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5431695 {A : Type'} (f : nat -> A) : (term1580 A f) = (term1580 A f).
Proof. exact (MK_COMB (@lem5431694) (@lem5431693 A f)). Qed.
Lemma lem5431696 {A : Type'} : (term1581 A) = (term1581 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5431695 A f)). Qed.
Lemma lem5431697 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5431699 {A : Type'} : (term1582 A) = (term1582 A).
Proof. exact (MK_COMB (@lem5431697 A) (@lem5431696 A)). Qed.
Lemma lem5431700 {A : Type'} (h1 : term15 A) : term1582 A.
Proof. exact (EQ_MP (@lem5431699 A) (@lem5428409 A h1)). Qed.
Lemma lem5432573 (_70060 : nat) (h1 : term105) : term1845 _70060.
Proof. exact (@lem5430828 h1 _70060). Qed.
Lemma lem5432574 (_70060 : nat) : (term1845 _70060) = (term1587 _70060).
Proof. exact (eq_refl (term1845 _70060)). Qed.
Lemma lem5432575 (_70060 : nat) (h1 : term105) : term1587 _70060.
Proof. exact (EQ_MP (@lem5432574 _70060) (@lem5432573 _70060 h1)). Qed.
Lemma lem5432576 (_70060 : nat) (_70061 : nat) (h1 : term105) : term1846 _70060 _70061.
Proof. exact (@lem5432575 _70060 h1 _70061). Qed.
Lemma lem5432577 (_70060 : nat) (_70061 : nat) : (term1846 _70060 _70061) = (term1585 _70060 _70061).
Proof. exact (eq_refl (term1846 _70060 _70061)). Qed.
Lemma lem5432585 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1847 A f'' _70064.
Proof. exact (@lem5431068 A i'' j'' f'' h1 _70064). Qed.
Lemma lem5432586 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1847 A f'' _70064) = (term1827 A f'' _70064).
Proof. exact (eq_refl (term1847 A f'' _70064)). Qed.
Lemma lem5432587 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1827 A f'' _70064.
Proof. exact (EQ_MP (@lem5432586 A f'' _70064) (@lem5432585 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5432588 {A : Type'} (_70064 : A -> Prop) (_70065 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1848 A f'' _70064 _70065.
Proof. exact (@lem5432587 A _70064 i'' j'' f'' h1 _70065). Qed.
Lemma lem5432589 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) : (term1848 A f'' _70064 _70065) = (term1825 A _70065 f'' _70064).
Proof. exact (eq_refl (term1848 A f'' _70064 _70065)). Qed.
Lemma lem5432590 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1825 A _70065 f'' _70064.
Proof. exact (EQ_MP (@lem5432589 A _70065 f'' _70064) (@lem5432588 A _70064 _70065 i'' j'' f'' h1)). Qed.
Lemma lem5432591 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1849 A _70065 f'' _70064 _70066.
Proof. exact (@lem5432590 A _70065 _70064 i'' j'' f'' h1 _70066). Qed.
Lemma lem5432592 {A : Type'} (_70065 : nat) (_70066 : nat) (f'' : type681 A) (_70064 : A -> Prop) : (term1849 A _70065 f'' _70064 _70066) = (term1823 A _70065 _70066 f'' _70064).
Proof. exact (eq_refl (term1849 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5432593 {A : Type'} (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1823 A _70065 _70066 f'' _70064.
Proof. exact (EQ_MP (@lem5432592 A _70065 _70066 f'' _70064) (@lem5432591 A _70065 _70064 _70066 i'' j'' f'' h1)). Qed.
Lemma lem5432624 {A : Type'} (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1850 A i''' j''' s _70077.
Proof. exact (@lem5431604 A i''' j''' s h1 _70077). Qed.
Lemma lem5432625 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70077 : nat -> Prop) : (term1850 A i''' j''' s _70077) = (term1842 A i''' j''' s _70077).
Proof. exact (eq_refl (term1850 A i''' j''' s _70077)). Qed.
Lemma lem5432626 {A : Type'} (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1842 A i''' j''' s _70077.
Proof. exact (EQ_MP (@lem5432625 A i''' j''' s _70077) (@lem5432624 A _70077 i''' j''' s h1)). Qed.
Lemma lem5432627 {A : Type'} (_70077 : nat -> Prop) (_70078 : nat -> A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1851 A i''' j''' s _70077 _70078.
Proof. exact (@lem5432626 A _70077 i''' j''' s h1 _70078). Qed.
Lemma lem5432628 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1851 A i''' j''' s _70077 _70078) = (term1840 A i''' j''' s _70078 _70077).
Proof. exact (eq_refl (term1851 A i''' j''' s _70077 _70078)). Qed.
Lemma lem5432629 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1840 A i''' j''' s _70078 _70077.
Proof. exact (EQ_MP (@lem5432628 A i''' j''' s _70078 _70077) (@lem5432627 A _70077 _70078 i''' j''' s h1)). Qed.
Lemma lem5432660 {A : Type'} (_70089 : nat -> A) (h1 : term15 A) : term1852 A _70089.
Proof. exact (@lem5431700 A h1 _70089). Qed.
Lemma lem5432661 {A : Type'} (_70089 : nat -> A) : (term1852 A _70089) = (term1580 A _70089).
Proof. exact (eq_refl (term1852 A _70089)). Qed.
Lemma lem5432662 {A : Type'} (_70089 : nat -> A) (h1 : term15 A) : term1580 A _70089.
Proof. exact (EQ_MP (@lem5432661 A _70089) (@lem5432660 A _70089 h1)). Qed.
Lemma lem5432663 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) (h1 : term15 A) : term1853 A _70089 _70090.
Proof. exact (@lem5432662 A _70089 h1 _70090). Qed.
Lemma lem5432664 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1853 A _70089 _70090) = (term1578 A _70089 _70090).
Proof. exact (eq_refl (term1853 A _70089 _70090)). Qed.
Lemma lem5432742 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1837 A i''' j''' s _70078 _70077.
Proof. exact (proj1 (@lem5432629 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5432743 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1835 A i''' j''' s _70078 _70077.
Proof. exact (proj2 (@lem5432742 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5432764 {A : Type'} (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1854 A f'' _70064 _70065 _70066.
Proof. exact (proj1 (@lem5432593 A _70065 _70066 _70064 i'' j'' f'' h1)). Qed.
Lemma lem5432862 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1831 A i''' j''' s _70078 _70077.
Proof. exact (proj2 (@lem5432629 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5432872 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1855 A i''' s _70078 _70077.
Proof. exact (proj1 (@lem5432742 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5432882 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1855 A j''' s _70078 _70077.
Proof. exact (proj1 (@lem5432743 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5432892 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1856 A i''' j''' s _70078 _70077.
Proof. exact (proj2 (@lem5432743 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5433032 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1625 A f'' _70064 _70065 _70066) = (term1857 A f'' _70064 _70065 _70066).
Proof. exact (@lem5423188 (term1616 A _70065 _70064) (term1619 A _70065 f'' _70064 _70066) (_70065 = _70066)). Qed.
Lemma lem5433039 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1858 A f'' _70064 _70065 _70066) = (term1859 A f'' _70064 _70065 _70066).
Proof. exact (@lem5423188 (term1616 A _70066 _70064) (term1611 A _70065 f'' _70064 _70066) (_70065 = _70066)). Qed.
Lemma lem5433040 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) : (term1617 A _70065 _70064) = (term1617 A _70065 _70064).
Proof. exact (eq_refl (term1617 A _70065 _70064)). Qed.
Lemma lem5433043 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1857 A f'' _70064 _70065 _70066) = (term1860 A f'' _70064 _70065 _70066).
Proof. exact (MK_COMB (@lem5433040 A _70065 _70064) (@lem5433039 A f'' _70064 _70065 _70066)). Qed.
Lemma lem5433045 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1625 A f'' _70064 _70065 _70066) = (term1860 A f'' _70064 _70065 _70066).
Proof. exact (TRANS (@lem5433032 A f'' _70064 _70065 _70066) (@lem5433043 A f'' _70064 _70065 _70066)). Qed.
Lemma lem5433046 {A : Type'} (_70064 : A -> Prop) : (term1639 A _70064) = (term1639 A _70064).
Proof. exact (eq_refl (term1639 A _70064)). Qed.
Lemma lem5433049 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1854 A f'' _70064 _70065 _70066) = (term1861 A f'' _70064 _70065 _70066).
Proof. exact (MK_COMB (@lem5433046 A _70064) (@lem5433045 A f'' _70064 _70065 _70066)). Qed.
Lemma lem5433050 {A : Type'} (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1861 A f'' _70064 _70065 _70066.
Proof. exact (EQ_MP (@lem5433049 A f'' _70064 _70065 _70066) (@lem5432764 A _70064 _70065 _70066 i'' j'' f'' h1)). Qed.
Lemma lem5433056 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1862 A f'' _70064.
Proof. exact (proj2 (@lem5432593 A (@el nat) (@el nat) _70064 i'' j'' f'' h1)). Qed.
Lemma lem5433154 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1638 A s.
Proof. exact (proj1 (@lem5430666 A s f''' k h1)). Qed.
Lemma lem5433176 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : s = (term1573 A f''' k).
Proof. exact (proj2 (@lem5430671 A s f''' k h1)). Qed.
Lemma lem5433478 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) (h1 : term15 A) : term1578 A _70089 _70090.
Proof. exact (EQ_MP (@lem5432664 A _70089 _70090) (@lem5432663 A _70089 _70090 h1)). Qed.
Lemma lem5433535 {A : Type'} : (term1863 A) = (term1863 A).
Proof. exact (eq_refl (term1863 A)). Qed.
Lemma lem5433536 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : (term1864 A s) = (term1865 A f''' k).
Proof. exact (MK_COMB (@lem5433535 A) (@lem5433176 A s f''' k h1)). Qed.
Lemma lem5433537 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (term1865 A f''' k) = (term1866 A f''' k).
Proof. exact (eq_refl (term1865 A f''' k)). Qed.
Lemma lem5433538 {A : Type'} (s : A -> Prop) : (term1867 A s) = (term1867 A s).
Proof. exact (eq_refl (term1867 A s)). Qed.
Lemma lem5433539 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : ((term1864 A s) = (term1865 A f''' k)) = ((term1864 A s) = (term1866 A f''' k)).
Proof. exact (MK_COMB (@lem5433538 A s) (@lem5433537 A f''' k)). Qed.
Lemma lem5433540 {A : Type'} (s : A -> Prop) : (term1864 A s) = (term1638 A s).
Proof. exact (eq_refl (term1864 A s)). Qed.
Lemma lem5433541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5433542 {A : Type'} (s : A -> Prop) : (term1867 A s) = (term1868 A s).
Proof. exact (MK_COMB (@lem5433541) (@lem5433540 A s)). Qed.
Lemma lem5433543 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (term1866 A f''' k) = (term1866 A f''' k).
Proof. exact (eq_refl (term1866 A f''' k)). Qed.
Lemma lem5433544 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : ((term1864 A s) = (term1866 A f''' k)) = ((term1638 A s) = (term1866 A f''' k)).
Proof. exact (MK_COMB (@lem5433542 A s) (@lem5433543 A f''' k)). Qed.
Lemma lem5433545 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) : ((term1864 A s) = (term1865 A f''' k)) = ((term1638 A s) = (term1866 A f''' k)).
Proof. exact (TRANS (@lem5433539 A s f''' k) (@lem5433544 A s f''' k)). Qed.
Lemma lem5433546 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : (term1638 A s) = (term1866 A f''' k).
Proof. exact (EQ_MP (@lem5433545 A s f''' k) (@lem5433536 A s f''' k h1)). Qed.
Lemma lem5433547 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1866 A f''' k.
Proof. exact (EQ_MP (@lem5433546 A s f''' k h1) (@lem5433154 A s f''' k h1)). Qed.
Lemma lem5434564 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5434565 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1869 A s.
Proof. exact (fun h0 : term1638 A s => @lem5434564 A i''' j''' s h1). Qed.
Lemma lem5434567 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434568 {A : Type'} (s : A -> Prop) : (term1869 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5434567 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5434569 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5434568 A s) (@lem5434565 A i''' j''' s h1)). Qed.
Lemma lem5434571 (_70060 : nat) (_70061 : nat) (h1 : term105) : term1585 _70060 _70061.
Proof. exact (EQ_MP (@lem5432577 _70060 _70061) (@lem5432576 _70060 _70061 h1)). Qed.
Lemma lem5434572 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (@lem5434571 term1592 (@I ((A -> Prop) -> nat) (@CARD A) s) h1). Qed.
Lemma lem5434573 {A : Type'} (s : A -> Prop) (h1 : term105) : term1872 A s.
Proof. exact (fun h0 : term1873 A s => @lem5434572 A s h1). Qed.
Lemma lem5434575 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434576 {A : Type'} (s : A -> Prop) : (term1872 A s) = (term1871 A s).
Proof. exact (@lem5434575 (term1871 A s)). Qed.
Lemma lem5434577 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (EQ_MP (@lem5434576 A s) (@lem5434573 A s h1)). Qed.
Lemma lem5434579 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5434580 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1869 A s.
Proof. exact (fun h0 : term1638 A s => @lem5434579 A i''' j''' s h1). Qed.
Lemma lem5434582 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434583 {A : Type'} (s : A -> Prop) : (term1869 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5434582 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5434584 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5434583 A s) (@lem5434580 A i''' j''' s h1)). Qed.
Lemma lem5434590 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5434591 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1862 A f'' _70064) = (term1874 A f'' _70064).
Proof. exact (@lem5434590 (_70064 = (term1606 A f'' _70064)) (term1638 A _70064)). Qed.
Lemma lem5434599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5434600 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1875 A f'' _70064) = (term1876 A f'' _70064).
Proof. exact (MK_COMB (@lem5434599) (@lem5434591 A f'' _70064)). Qed.
Lemma lem5434608 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1874 A f'' _70064) = (term1874 A f'' _70064).
Proof. exact (eq_refl (term1874 A f'' _70064)). Qed.
Lemma lem5434609 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : ((term1862 A f'' _70064) = (term1874 A f'' _70064)) = ((term1874 A f'' _70064) = (term1874 A f'' _70064)).
Proof. exact (MK_COMB (@lem5434600 A f'' _70064) (@lem5434608 A f'' _70064)). Qed.
Lemma lem5434611 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5434612 (x : Prop) : (x = x) = True.
Proof. exact (@lem5434611 Prop x). Qed.
Lemma lem5434613 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : ((term1874 A f'' _70064) = (term1874 A f'' _70064)) = True.
Proof. exact (@lem5434612 (term1874 A f'' _70064)). Qed.
Lemma lem5434614 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : ((term1862 A f'' _70064) = (term1874 A f'' _70064)) = True.
Proof. exact (TRANS (@lem5434609 A f'' _70064) (@lem5434613 A f'' _70064)). Qed.
Lemma lem5434615 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : True = ((term1862 A f'' _70064) = (term1874 A f'' _70064)).
Proof. exact (SYM (@lem5434614 A f'' _70064)). Qed.
Lemma lem5434616 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1862 A f'' _70064) = (term1874 A f'' _70064).
Proof. exact (EQ_MP (@lem5434615 A f'' _70064) (@lem0)). Qed.
Lemma lem5434617 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1874 A f'' _70064.
Proof. exact (EQ_MP (@lem5434616 A f'' _70064) (@lem5433056 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5434619 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5434620 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1874 A f'' _70064) = (term1878 A f'' _70064).
Proof. exact (@lem5434619 (term1638 A _70064) (_70064 = (term1606 A f'' _70064))). Qed.
Lemma lem5434622 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434623 {A : Type'} (_70064 : A -> Prop) : (term1880 A _70064) = (@I ((A -> Prop) -> Prop) (@FINITE A) _70064).
Proof. exact (@lem5434622 (@I ((A -> Prop) -> Prop) (@FINITE A) _70064)). Qed.
Lemma lem5434624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5434625 {A : Type'} (_70064 : A -> Prop) : (term1881 A _70064) = (term1882 A _70064).
Proof. exact (MK_COMB (@lem5434624) (@lem5434623 A _70064)). Qed.
Lemma lem5434626 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (_70064 = (term1606 A f'' _70064)) = (_70064 = (term1606 A f'' _70064)).
Proof. exact (eq_refl (_70064 = (term1606 A f'' _70064))). Qed.
Lemma lem5434627 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1878 A f'' _70064) = (term1883 A f'' _70064).
Proof. exact (MK_COMB (@lem5434625 A _70064) (@lem5434626 A f'' _70064)). Qed.
Lemma lem5434628 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) : (term1874 A f'' _70064) = (term1883 A f'' _70064).
Proof. exact (TRANS (@lem5434620 A f'' _70064) (@lem5434627 A f'' _70064)). Qed.
Lemma lem5434631 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (EQ_MP (@lem5434628 A f'' _70064) (@lem5434617 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5434632 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (@lem5434631 A _70064 i'' j'' f'' h1). Qed.
Lemma lem5434633 {A : Type'} (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' s.
Proof. exact (@lem5434632 A s i'' j'' f'' h1). Qed.
Lemma lem5434636 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (@lem5434633 A s i'' j'' f'' h1 (@lem5434584 A i''' j''' s h2)). Qed.
Lemma lem5434637 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : term1884 A f'' s.
Proof. exact (fun h0 : term1885 A f'' s => @lem5434636 A i'' j'' f'' i''' j''' s h1 h2). Qed.
Lemma lem5434639 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434640 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1884 A f'' s) = (s = (term1606 A f'' s)).
Proof. exact (@lem5434639 (s = (term1606 A f'' s))). Qed.
Lemma lem5434641 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (EQ_MP (@lem5434640 A f'' s) (@lem5434637 A i'' j'' f'' i''' j''' s h1 h2)). Qed.
Lemma lem5434643 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5434644 {A : Type'} (s : A -> Prop) (i''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1855 A i''' s _70078 _70077) = (term1886 A s i''' _70078 _70077).
Proof. exact (@lem5434643 (term1713 A s _70078 _70077) (term1730 A i''' _70078 _70077)). Qed.
Lemma lem5434646 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5434647 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1890 A s _70078 _70077).
Proof. exact (@lem5434646 (term1576 _70077) (term1712 A s _70078 _70077)). Qed.
Lemma lem5434649 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434650 (_70077 : nat -> Prop) : (term1891 _70077) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077).
Proof. exact (@lem5434649 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077)). Qed.
Lemma lem5434651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5434652 (_70077 : nat -> Prop) : (term1892 _70077) = (term1689 _70077).
Proof. exact (MK_COMB (@lem5434651) (@lem5434650 _70077)). Qed.
Lemma lem5434654 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434655 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1893 A s _70078 _70077) = (s = (term1573 A _70078 _70077)).
Proof. exact (@lem5434654 (s = (term1573 A _70078 _70077))). Qed.
Lemma lem5434656 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1890 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434652 _70077) (@lem5434655 A s _70078 _70077)). Qed.
Lemma lem5434657 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (TRANS (@lem5434647 A s _70078 _70077) (@lem5434656 A s _70078 _70077)). Qed.
Lemma lem5434658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5434659 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1894 A s _70078 _70077) = (term1895 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434658) (@lem5434657 A s _70078 _70077)). Qed.
Lemma lem5434660 {A : Type'} (i''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1730 A i''' _70078 _70077) = (term1730 A i''' _70078 _70077).
Proof. exact (eq_refl (term1730 A i''' _70078 _70077)). Qed.
Lemma lem5434661 {A : Type'} (s : A -> Prop) (i''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1886 A s i''' _70078 _70077) = (term1896 A s i''' _70078 _70077).
Proof. exact (MK_COMB (@lem5434659 A s _70078 _70077) (@lem5434660 A i''' _70078 _70077)). Qed.
Lemma lem5434662 {A : Type'} (s : A -> Prop) (i''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1855 A i''' s _70078 _70077) = (term1896 A s i''' _70078 _70077).
Proof. exact (TRANS (@lem5434644 A s i''' _70078 _70077) (@lem5434661 A s i''' _70078 _70077)). Qed.
Lemma lem5434664 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1897 A f'' s.
Proof. exact (conj (@lem5434577 A s h1) (@lem5434641 A i'' j'' f'' i''' j''' s h2 h3)). Qed.
Lemma lem5434666 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1896 A s i''' _70078 _70077.
Proof. exact (EQ_MP (@lem5434662 A s i''' _70078 _70077) (@lem5432872 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5434667 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1896 A s i''' _70078 _70077.
Proof. exact (@lem5434666 A _70078 _70077 i''' j''' s h1). Qed.
Lemma lem5434668 {A : Type'} (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1898 A i''' f'' s.
Proof. exact (@lem5434667 A (@I ((A -> Prop) -> nat -> A) f'' s) (term1599 A s) i''' j''' s h1). Qed.
Lemma lem5434671 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1899 A i''' f'' s.
Proof. exact (@lem5434668 A f'' i''' j''' s h3 (@lem5434664 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434672 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1900 A i''' f'' s.
Proof. exact (fun h0 : term1901 A i''' f'' s => @lem5434671 A i'' j'' f'' i''' j''' s h1 h2 h3). Qed.
Lemma lem5434674 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434675 {A : Type'} (i''' : type984 A) (f'' : type681 A) (s : A -> Prop) : (term1900 A i''' f'' s) = (term1899 A i''' f'' s).
Proof. exact (@lem5434674 (term1899 A i''' f'' s)). Qed.
Lemma lem5434676 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1899 A i''' f'' s.
Proof. exact (EQ_MP (@lem5434675 A i''' f'' s) (@lem5434672 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434678 (_70060 : nat) (_70061 : nat) (h1 : term105) : term1585 _70060 _70061.
Proof. exact (EQ_MP (@lem5432577 _70060 _70061) (@lem5432576 _70060 _70061 h1)). Qed.
Lemma lem5434679 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (@lem5434678 term1592 (@I ((A -> Prop) -> nat) (@CARD A) s) h1). Qed.
Lemma lem5434680 {A : Type'} (s : A -> Prop) (h1 : term105) : term1872 A s.
Proof. exact (fun h0 : term1873 A s => @lem5434679 A s h1). Qed.
Lemma lem5434682 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434683 {A : Type'} (s : A -> Prop) : (term1872 A s) = (term1871 A s).
Proof. exact (@lem5434682 (term1871 A s)). Qed.
Lemma lem5434684 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (EQ_MP (@lem5434683 A s) (@lem5434680 A s h1)). Qed.
Lemma lem5434686 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5434687 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1869 A s.
Proof. exact (fun h0 : term1638 A s => @lem5434686 A i''' j''' s h1). Qed.
Lemma lem5434689 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434690 {A : Type'} (s : A -> Prop) : (term1869 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5434689 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5434691 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5434690 A s) (@lem5434687 A i''' j''' s h1)). Qed.
Lemma lem5434693 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (EQ_MP (@lem5434628 A f'' _70064) (@lem5434617 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5434694 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (@lem5434693 A _70064 i'' j'' f'' h1). Qed.
Lemma lem5434695 {A : Type'} (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' s.
Proof. exact (@lem5434694 A s i'' j'' f'' h1). Qed.
Lemma lem5434698 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (@lem5434695 A s i'' j'' f'' h1 (@lem5434691 A i''' j''' s h2)). Qed.
Lemma lem5434699 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : term1884 A f'' s.
Proof. exact (fun h0 : term1885 A f'' s => @lem5434698 A i'' j'' f'' i''' j''' s h1 h2). Qed.
Lemma lem5434701 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434702 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1884 A f'' s) = (s = (term1606 A f'' s)).
Proof. exact (@lem5434701 (s = (term1606 A f'' s))). Qed.
Lemma lem5434703 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (EQ_MP (@lem5434702 A f'' s) (@lem5434699 A i'' j'' f'' i''' j''' s h1 h2)). Qed.
Lemma lem5434705 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5434706 {A : Type'} (s : A -> Prop) (j''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1855 A j''' s _70078 _70077) = (term1886 A s j''' _70078 _70077).
Proof. exact (@lem5434705 (term1713 A s _70078 _70077) (term1730 A j''' _70078 _70077)). Qed.
Lemma lem5434708 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5434709 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1890 A s _70078 _70077).
Proof. exact (@lem5434708 (term1576 _70077) (term1712 A s _70078 _70077)). Qed.
Lemma lem5434711 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434712 (_70077 : nat -> Prop) : (term1891 _70077) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077).
Proof. exact (@lem5434711 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077)). Qed.
Lemma lem5434713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5434714 (_70077 : nat -> Prop) : (term1892 _70077) = (term1689 _70077).
Proof. exact (MK_COMB (@lem5434713) (@lem5434712 _70077)). Qed.
Lemma lem5434716 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434717 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1893 A s _70078 _70077) = (s = (term1573 A _70078 _70077)).
Proof. exact (@lem5434716 (s = (term1573 A _70078 _70077))). Qed.
Lemma lem5434718 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1890 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434714 _70077) (@lem5434717 A s _70078 _70077)). Qed.
Lemma lem5434719 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (TRANS (@lem5434709 A s _70078 _70077) (@lem5434718 A s _70078 _70077)). Qed.
Lemma lem5434720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5434721 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1894 A s _70078 _70077) = (term1895 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434720) (@lem5434719 A s _70078 _70077)). Qed.
Lemma lem5434722 {A : Type'} (j''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1730 A j''' _70078 _70077) = (term1730 A j''' _70078 _70077).
Proof. exact (eq_refl (term1730 A j''' _70078 _70077)). Qed.
Lemma lem5434723 {A : Type'} (s : A -> Prop) (j''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1886 A s j''' _70078 _70077) = (term1896 A s j''' _70078 _70077).
Proof. exact (MK_COMB (@lem5434721 A s _70078 _70077) (@lem5434722 A j''' _70078 _70077)). Qed.
Lemma lem5434724 {A : Type'} (s : A -> Prop) (j''' : type984 A) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1855 A j''' s _70078 _70077) = (term1896 A s j''' _70078 _70077).
Proof. exact (TRANS (@lem5434706 A s j''' _70078 _70077) (@lem5434723 A s j''' _70078 _70077)). Qed.
Lemma lem5434726 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1897 A f'' s.
Proof. exact (conj (@lem5434684 A s h1) (@lem5434703 A i'' j'' f'' i''' j''' s h2 h3)). Qed.
Lemma lem5434728 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1896 A s j''' _70078 _70077.
Proof. exact (EQ_MP (@lem5434724 A s j''' _70078 _70077) (@lem5432882 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5434729 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1896 A s j''' _70078 _70077.
Proof. exact (@lem5434728 A _70078 _70077 i''' j''' s h1). Qed.
Lemma lem5434730 {A : Type'} (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1898 A j''' f'' s.
Proof. exact (@lem5434729 A (@I ((A -> Prop) -> nat -> A) f'' s) (term1599 A s) i''' j''' s h1). Qed.
Lemma lem5434733 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1899 A j''' f'' s.
Proof. exact (@lem5434730 A f'' i''' j''' s h3 (@lem5434726 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434734 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1900 A j''' f'' s.
Proof. exact (fun h0 : term1901 A j''' f'' s => @lem5434733 A i'' j'' f'' i''' j''' s h1 h2 h3). Qed.
Lemma lem5434736 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434737 {A : Type'} (j''' : type984 A) (f'' : type681 A) (s : A -> Prop) : (term1900 A j''' f'' s) = (term1899 A j''' f'' s).
Proof. exact (@lem5434736 (term1899 A j''' f'' s)). Qed.
Lemma lem5434738 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1899 A j''' f'' s.
Proof. exact (EQ_MP (@lem5434737 A j''' f'' s) (@lem5434734 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434740 (_70060 : nat) (_70061 : nat) (h1 : term105) : term1585 _70060 _70061.
Proof. exact (EQ_MP (@lem5432577 _70060 _70061) (@lem5432576 _70060 _70061 h1)). Qed.
Lemma lem5434741 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (@lem5434740 term1592 (@I ((A -> Prop) -> nat) (@CARD A) s) h1). Qed.
Lemma lem5434742 {A : Type'} (s : A -> Prop) (h1 : term105) : term1872 A s.
Proof. exact (fun h0 : term1873 A s => @lem5434741 A s h1). Qed.
Lemma lem5434744 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434745 {A : Type'} (s : A -> Prop) : (term1872 A s) = (term1871 A s).
Proof. exact (@lem5434744 (term1871 A s)). Qed.
Lemma lem5434746 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (EQ_MP (@lem5434745 A s) (@lem5434742 A s h1)). Qed.
Lemma lem5434748 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5434749 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1869 A s.
Proof. exact (fun h0 : term1638 A s => @lem5434748 A i''' j''' s h1). Qed.
Lemma lem5434751 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434752 {A : Type'} (s : A -> Prop) : (term1869 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5434751 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5434753 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5434752 A s) (@lem5434749 A i''' j''' s h1)). Qed.
Lemma lem5434755 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (EQ_MP (@lem5434628 A f'' _70064) (@lem5434617 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5434756 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (@lem5434755 A _70064 i'' j'' f'' h1). Qed.
Lemma lem5434757 {A : Type'} (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' s.
Proof. exact (@lem5434756 A s i'' j'' f'' h1). Qed.
Lemma lem5434760 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (@lem5434757 A s i'' j'' f'' h1 (@lem5434753 A i''' j''' s h2)). Qed.
Lemma lem5434761 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : term1884 A f'' s.
Proof. exact (fun h0 : term1885 A f'' s => @lem5434760 A i'' j'' f'' i''' j''' s h1 h2). Qed.
Lemma lem5434763 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434764 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1884 A f'' s) = (s = (term1606 A f'' s)).
Proof. exact (@lem5434763 (s = (term1606 A f'' s))). Qed.
Lemma lem5434765 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (EQ_MP (@lem5434764 A f'' s) (@lem5434761 A i'' j'' f'' i''' j''' s h1 h2)). Qed.
Lemma lem5434767 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5434768 {A : Type'} (s : A -> Prop) (i''' : type984 A) (j''' : type984 A) (_70077 : nat -> Prop) (_70078 : nat -> A) : (term1856 A i''' j''' s _70078 _70077) = (term1902 A s i''' j''' _70077 _70078).
Proof. exact (@lem5434767 (term1713 A s _70078 _70077) ((term1721 A i''' _70077 _70078) = (term1721 A j''' _70077 _70078))). Qed.
Lemma lem5434770 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5434771 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1890 A s _70078 _70077).
Proof. exact (@lem5434770 (term1576 _70077) (term1712 A s _70078 _70077)). Qed.
Lemma lem5434773 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434774 (_70077 : nat -> Prop) : (term1891 _70077) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077).
Proof. exact (@lem5434773 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077)). Qed.
Lemma lem5434775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5434776 (_70077 : nat -> Prop) : (term1892 _70077) = (term1689 _70077).
Proof. exact (MK_COMB (@lem5434775) (@lem5434774 _70077)). Qed.
Lemma lem5434778 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5434779 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1893 A s _70078 _70077) = (s = (term1573 A _70078 _70077)).
Proof. exact (@lem5434778 (s = (term1573 A _70078 _70077))). Qed.
Lemma lem5434780 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1890 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434776 _70077) (@lem5434779 A s _70078 _70077)). Qed.
Lemma lem5434781 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1889 A s _70078 _70077) = (term1690 A s _70078 _70077).
Proof. exact (TRANS (@lem5434771 A s _70078 _70077) (@lem5434780 A s _70078 _70077)). Qed.
Lemma lem5434782 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5434783 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1894 A s _70078 _70077) = (term1895 A s _70078 _70077).
Proof. exact (MK_COMB (@lem5434782) (@lem5434781 A s _70078 _70077)). Qed.
Lemma lem5434784 {A : Type'} (i''' : type984 A) (j''' : type984 A) (_70077 : nat -> Prop) (_70078 : nat -> A) : ((term1721 A i''' _70077 _70078) = (term1721 A j''' _70077 _70078)) = ((term1721 A i''' _70077 _70078) = (term1721 A j''' _70077 _70078)).
Proof. exact (eq_refl ((term1721 A i''' _70077 _70078) = (term1721 A j''' _70077 _70078))). Qed.
Lemma lem5434785 {A : Type'} (s : A -> Prop) (i''' : type984 A) (j''' : type984 A) (_70077 : nat -> Prop) (_70078 : nat -> A) : (term1902 A s i''' j''' _70077 _70078) = (term1903 A s i''' j''' _70077 _70078).
Proof. exact (MK_COMB (@lem5434783 A s _70078 _70077) (@lem5434784 A i''' j''' _70077 _70078)). Qed.
Lemma lem5434786 {A : Type'} (s : A -> Prop) (i''' : type984 A) (j''' : type984 A) (_70077 : nat -> Prop) (_70078 : nat -> A) : (term1856 A i''' j''' s _70078 _70077) = (term1903 A s i''' j''' _70077 _70078).
Proof. exact (TRANS (@lem5434768 A s i''' j''' _70077 _70078) (@lem5434785 A s i''' j''' _70077 _70078)). Qed.
Lemma lem5434788 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1897 A f'' s.
Proof. exact (conj (@lem5434746 A s h1) (@lem5434765 A i'' j'' f'' i''' j''' s h2 h3)). Qed.
Lemma lem5434790 {A : Type'} (_70077 : nat -> Prop) (_70078 : nat -> A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1903 A s i''' j''' _70077 _70078.
Proof. exact (EQ_MP (@lem5434786 A s i''' j''' _70077 _70078) (@lem5432892 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5434791 {A : Type'} (_70077 : nat -> Prop) (_70078 : nat -> A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1903 A s i''' j''' _70077 _70078.
Proof. exact (@lem5434790 A _70077 _70078 i''' j''' s h1). Qed.
Lemma lem5434792 {A : Type'} (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1904 A i''' j''' f'' s.
Proof. exact (@lem5434791 A (term1599 A s) (@I ((A -> Prop) -> nat -> A) f'' s) i''' j''' s h1). Qed.
Lemma lem5434795 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : (term1905 A i''' f'' s) = (term1905 A j''' f'' s).
Proof. exact (@lem5434792 A f'' i''' j''' s h3 (@lem5434788 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434796 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1906 A i''' j''' f'' s.
Proof. exact (fun h0 : term1907 A i''' j''' f'' s => @lem5434795 A i'' j'' f'' i''' j''' s h1 h2 h3). Qed.
Lemma lem5434798 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5434799 {A : Type'} (i''' : type984 A) (j''' : type984 A) (f'' : type681 A) (s : A -> Prop) : (term1906 A i''' j''' f'' s) = ((term1905 A i''' f'' s) = (term1905 A j''' f'' s)).
Proof. exact (@lem5434798 ((term1905 A i''' f'' s) = (term1905 A j''' f'' s))). Qed.
Lemma lem5434800 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : (term1905 A i''' f'' s) = (term1905 A j''' f'' s).
Proof. exact (EQ_MP (@lem5434799 A i''' j''' f'' s) (@lem5434796 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5434826 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434827 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1859 A f'' _70064 _70065 _70066) = (term1908 A f'' _70064 _70065 _70066).
Proof. exact (@lem5434826 (term1611 A _70065 f'' _70064 _70066) (term1616 A _70066 _70064) (_70065 = _70066)). Qed.
Lemma lem5434843 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5434844 {A : Type'} (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1909 A _70064 _70065 _70066) = (term1910 A _70065 _70066 _70064).
Proof. exact (@lem5434843 (_70065 = _70066) (term1616 A _70066 _70064)). Qed.
Lemma lem5434852 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1911 A _70065 f'' _70064 _70066) = (term1911 A _70065 f'' _70064 _70066).
Proof. exact (eq_refl (term1911 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5434853 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1908 A f'' _70064 _70065 _70066) = (term1912 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5434852 A _70065 f'' _70064 _70066) (@lem5434844 A _70065 _70066 _70064)). Qed.
Lemma lem5434857 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434858 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1912 A f'' _70065 _70066 _70064) = (term1913 A _70065 f'' _70066 _70064).
Proof. exact (@lem5434857 (_70065 = _70066) (term1611 A _70065 f'' _70064 _70066) (term1616 A _70066 _70064)). Qed.
Lemma lem5434878 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1908 A f'' _70064 _70065 _70066) = (term1913 A _70065 f'' _70066 _70064).
Proof. exact (TRANS (@lem5434853 A f'' _70065 _70066 _70064) (@lem5434858 A _70065 f'' _70066 _70064)). Qed.
Lemma lem5434879 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1859 A f'' _70064 _70065 _70066) = (term1913 A _70065 f'' _70066 _70064).
Proof. exact (TRANS (@lem5434827 A f'' _70064 _70065 _70066) (@lem5434878 A _70065 f'' _70066 _70064)). Qed.
Lemma lem5434880 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) : (term1617 A _70065 _70064) = (term1617 A _70065 _70064).
Proof. exact (eq_refl (term1617 A _70065 _70064)). Qed.
Lemma lem5434881 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1860 A f'' _70064 _70065 _70066) = (term1914 A _70065 f'' _70066 _70064).
Proof. exact (MK_COMB (@lem5434880 A _70065 _70064) (@lem5434879 A _70065 f'' _70066 _70064)). Qed.
Lemma lem5434885 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434886 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1914 A _70065 f'' _70066 _70064) = (term1915 A _70065 f'' _70066 _70064).
Proof. exact (@lem5434885 (_70065 = _70066) (term1616 A _70065 _70064) (term1916 A _70065 f'' _70066 _70064)). Qed.
Lemma lem5434902 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434903 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1917 A _70065 f'' _70066 _70064) = (term1918 A f'' _70065 _70066 _70064).
Proof. exact (@lem5434902 (term1611 A _70065 f'' _70064 _70066) (term1616 A _70065 _70064) (term1616 A _70066 _70064)). Qed.
Lemma lem5434921 (_70065 : nat) (_70066 : nat) : (term1919 _70065 _70066) = (term1919 _70065 _70066).
Proof. exact (eq_refl (term1919 _70065 _70066)). Qed.
Lemma lem5434922 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1915 A _70065 f'' _70066 _70064) = (term1920 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5434921 _70065 _70066) (@lem5434903 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434933 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1914 A _70065 f'' _70066 _70064) = (term1920 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5434886 A _70065 f'' _70066 _70064) (@lem5434922 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434934 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1860 A f'' _70064 _70065 _70066) = (term1920 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5434881 A _70065 f'' _70066 _70064) (@lem5434933 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434935 {A : Type'} (_70064 : A -> Prop) : (term1639 A _70064) = (term1639 A _70064).
Proof. exact (eq_refl (term1639 A _70064)). Qed.
Lemma lem5434936 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1861 A f'' _70064 _70065 _70066) = (term1921 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5434935 A _70064) (@lem5434934 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434940 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434941 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1921 A f'' _70065 _70066 _70064) = (term1922 A f'' _70065 _70066 _70064).
Proof. exact (@lem5434940 (_70065 = _70066) (term1638 A _70064) (term1918 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434957 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5434958 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1923 A f'' _70065 _70066 _70064) = (term1924 A f'' _70065 _70066 _70064).
Proof. exact (@lem5434957 (term1611 A _70065 f'' _70064 _70066) (term1638 A _70064) (term1925 A _70065 _70066 _70064)). Qed.
Lemma lem5434986 (_70065 : nat) (_70066 : nat) : (term1919 _70065 _70066) = (term1919 _70065 _70066).
Proof. exact (eq_refl (term1919 _70065 _70066)). Qed.
Lemma lem5434987 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1922 A f'' _70065 _70066 _70064) = (term1926 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5434986 _70065 _70066) (@lem5434958 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434998 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1921 A f'' _70065 _70066 _70064) = (term1926 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5434941 A f'' _70065 _70066 _70064) (@lem5434987 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5434999 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1861 A f'' _70064 _70065 _70066) = (term1926 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5434936 A f'' _70065 _70066 _70064) (@lem5434998 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5435001 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1927 A f'' _70064 _70065 _70066) = (term1928 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5435000) (@lem5434999 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435037 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5435038 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1619 A _70065 f'' _70064 _70066) = (term1916 A _70065 f'' _70066 _70064).
Proof. exact (@lem5435037 (term1611 A _70065 f'' _70064 _70066) (term1616 A _70066 _70064)). Qed.
Lemma lem5435046 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) : (term1617 A _70065 _70064) = (term1617 A _70065 _70064).
Proof. exact (eq_refl (term1617 A _70065 _70064)). Qed.
Lemma lem5435047 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70066 : nat) (_70064 : A -> Prop) : (term1621 A _70065 f'' _70064 _70066) = (term1917 A _70065 f'' _70066 _70064).
Proof. exact (MK_COMB (@lem5435046 A _70065 _70064) (@lem5435038 A _70065 f'' _70066 _70064)). Qed.
Lemma lem5435051 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5435052 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1917 A _70065 f'' _70066 _70064) = (term1918 A f'' _70065 _70066 _70064).
Proof. exact (@lem5435051 (term1611 A _70065 f'' _70064 _70066) (term1616 A _70065 _70064) (term1616 A _70066 _70064)). Qed.
Lemma lem5435070 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1621 A _70065 f'' _70064 _70066) = (term1918 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5435047 A _70065 f'' _70066 _70064) (@lem5435052 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435071 {A : Type'} (_70064 : A -> Prop) : (term1639 A _70064) = (term1639 A _70064).
Proof. exact (eq_refl (term1639 A _70064)). Qed.
Lemma lem5435072 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1929 A _70065 f'' _70064 _70066) = (term1923 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5435071 A _70064) (@lem5435070 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435076 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5435077 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1923 A f'' _70065 _70066 _70064) = (term1924 A f'' _70065 _70066 _70064).
Proof. exact (@lem5435076 (term1611 A _70065 f'' _70064 _70066) (term1638 A _70064) (term1925 A _70065 _70066 _70064)). Qed.
Lemma lem5435105 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1929 A _70065 f'' _70064 _70066) = (term1924 A f'' _70065 _70066 _70064).
Proof. exact (TRANS (@lem5435072 A f'' _70065 _70066 _70064) (@lem5435077 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435106 (_70065 : nat) (_70066 : nat) : (term1919 _70065 _70066) = (term1919 _70065 _70066).
Proof. exact (eq_refl (term1919 _70065 _70066)). Qed.
Lemma lem5435107 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : (term1930 A _70065 f'' _70064 _70066) = (term1926 A f'' _70065 _70066 _70064).
Proof. exact (MK_COMB (@lem5435106 _70065 _70066) (@lem5435105 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435118 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : ((term1861 A f'' _70064 _70065 _70066) = (term1930 A _70065 f'' _70064 _70066)) = ((term1926 A f'' _70065 _70066 _70064) = (term1926 A f'' _70065 _70066 _70064)).
Proof. exact (MK_COMB (@lem5435001 A f'' _70065 _70066 _70064) (@lem5435107 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435120 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5435121 (x : Prop) : (x = x) = True.
Proof. exact (@lem5435120 Prop x). Qed.
Lemma lem5435122 {A : Type'} (f'' : type681 A) (_70065 : nat) (_70066 : nat) (_70064 : A -> Prop) : ((term1926 A f'' _70065 _70066 _70064) = (term1926 A f'' _70065 _70066 _70064)) = True.
Proof. exact (@lem5435121 (term1926 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435123 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : ((term1861 A f'' _70064 _70065 _70066) = (term1930 A _70065 f'' _70064 _70066)) = True.
Proof. exact (TRANS (@lem5435118 A f'' _70065 _70066 _70064) (@lem5435122 A f'' _70065 _70066 _70064)). Qed.
Lemma lem5435124 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : True = ((term1861 A f'' _70064 _70065 _70066) = (term1930 A _70065 f'' _70064 _70066)).
Proof. exact (SYM (@lem5435123 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435125 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1861 A f'' _70064 _70065 _70066) = (term1930 A _70065 f'' _70064 _70066).
Proof. exact (EQ_MP (@lem5435124 A _70065 f'' _70064 _70066) (@lem0)). Qed.
Lemma lem5435126 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1930 A _70065 f'' _70064 _70066.
Proof. exact (EQ_MP (@lem5435125 A _70065 f'' _70064 _70066) (@lem5433050 A _70064 _70065 _70066 i'' j'' f'' h1)). Qed.
Lemma lem5435128 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5435129 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1930 A _70065 f'' _70064 _70066) = (term1931 A f'' _70064 _70065 _70066).
Proof. exact (@lem5435128 (term1929 A _70065 f'' _70064 _70066) (_70065 = _70066)). Qed.
Lemma lem5435131 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5435132 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1932 A _70065 f'' _70064 _70066) = (term1933 A _70065 f'' _70064 _70066).
Proof. exact (@lem5435131 (term1638 A _70064) (term1621 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435134 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5435135 {A : Type'} (_70064 : A -> Prop) : (term1880 A _70064) = (@I ((A -> Prop) -> Prop) (@FINITE A) _70064).
Proof. exact (@lem5435134 (@I ((A -> Prop) -> Prop) (@FINITE A) _70064)). Qed.
Lemma lem5435136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5435137 {A : Type'} (_70064 : A -> Prop) : (term1934 A _70064) = (term1750 A _70064).
Proof. exact (MK_COMB (@lem5435136) (@lem5435135 A _70064)). Qed.
Lemma lem5435139 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5435140 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1935 A _70065 f'' _70064 _70066) = (term1936 A _70065 f'' _70064 _70066).
Proof. exact (@lem5435139 (term1616 A _70065 _70064) (term1619 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435142 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5435143 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) : (term1937 A _70065 _70064) = (term1614 A _70065 _70064).
Proof. exact (@lem5435142 (term1614 A _70065 _70064)). Qed.
Lemma lem5435144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5435145 {A : Type'} (_70065 : nat) (_70064 : A -> Prop) : (term1938 A _70065 _70064) = (term1939 A _70065 _70064).
Proof. exact (MK_COMB (@lem5435144) (@lem5435143 A _70065 _70064)). Qed.
Lemma lem5435147 (a : Prop) (b : Prop) : (term1887 a b) = (term1888 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5435148 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1940 A _70065 f'' _70064 _70066) = (term1941 A _70065 f'' _70064 _70066).
Proof. exact (@lem5435147 (term1616 A _70066 _70064) (term1611 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435150 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5435151 {A : Type'} (_70066 : nat) (_70064 : A -> Prop) : (term1937 A _70066 _70064) = (term1614 A _70066 _70064).
Proof. exact (@lem5435150 (term1614 A _70066 _70064)). Qed.
Lemma lem5435152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5435153 {A : Type'} (_70066 : nat) (_70064 : A -> Prop) : (term1938 A _70066 _70064) = (term1939 A _70066 _70064).
Proof. exact (MK_COMB (@lem5435152) (@lem5435151 A _70066 _70064)). Qed.
Lemma lem5435155 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5435156 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1942 A _70065 f'' _70064 _70066) = ((term1607 A f'' _70064 _70065) = (term1607 A f'' _70064 _70066)).
Proof. exact (@lem5435155 ((term1607 A f'' _70064 _70065) = (term1607 A f'' _70064 _70066))). Qed.
Lemma lem5435157 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1941 A _70065 f'' _70064 _70066) = (term1943 A _70065 f'' _70064 _70066).
Proof. exact (MK_COMB (@lem5435153 A _70066 _70064) (@lem5435156 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435158 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1940 A _70065 f'' _70064 _70066) = (term1943 A _70065 f'' _70064 _70066).
Proof. exact (TRANS (@lem5435148 A _70065 f'' _70064 _70066) (@lem5435157 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435159 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1936 A _70065 f'' _70064 _70066) = (term1944 A _70065 f'' _70064 _70066).
Proof. exact (MK_COMB (@lem5435145 A _70065 _70064) (@lem5435158 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435160 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1935 A _70065 f'' _70064 _70066) = (term1944 A _70065 f'' _70064 _70066).
Proof. exact (TRANS (@lem5435140 A _70065 f'' _70064 _70066) (@lem5435159 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435161 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1933 A _70065 f'' _70064 _70066) = (term1945 A _70065 f'' _70064 _70066).
Proof. exact (MK_COMB (@lem5435137 A _70064) (@lem5435160 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435162 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1932 A _70065 f'' _70064 _70066) = (term1945 A _70065 f'' _70064 _70066).
Proof. exact (TRANS (@lem5435132 A _70065 f'' _70064 _70066) (@lem5435161 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5435164 {A : Type'} (_70065 : nat) (f'' : type681 A) (_70064 : A -> Prop) (_70066 : nat) : (term1946 A _70065 f'' _70064 _70066) = (term1947 A _70065 f'' _70064 _70066).
Proof. exact (MK_COMB (@lem5435163) (@lem5435162 A _70065 f'' _70064 _70066)). Qed.
Lemma lem5435165 (_70065 : nat) (_70066 : nat) : (_70065 = _70066) = (_70065 = _70066).
Proof. exact (eq_refl (_70065 = _70066)). Qed.
Lemma lem5435166 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1931 A f'' _70064 _70065 _70066) = (term1948 A f'' _70064 _70065 _70066).
Proof. exact (MK_COMB (@lem5435164 A _70065 f'' _70064 _70066) (@lem5435165 _70065 _70066)). Qed.
Lemma lem5435167 {A : Type'} (f'' : type681 A) (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) : (term1930 A _70065 f'' _70064 _70066) = (term1948 A f'' _70064 _70065 _70066).
Proof. exact (TRANS (@lem5435129 A f'' _70064 _70065 _70066) (@lem5435166 A f'' _70064 _70065 _70066)). Qed.
Lemma lem5435169 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1949 A i''' j''' f'' s.
Proof. exact (conj (@lem5434738 A i'' j'' f'' i''' j''' s h1 h2 h3) (@lem5434800 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435170 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1950 A i''' j''' f'' s.
Proof. exact (conj (@lem5434676 A i'' j'' f'' i''' j''' s h1 h2 h3) (@lem5435169 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435171 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1951 A i''' j''' f'' s.
Proof. exact (conj (@lem5434569 A i''' j''' s h3) (@lem5435170 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435173 {A : Type'} (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1948 A f'' _70064 _70065 _70066.
Proof. exact (EQ_MP (@lem5435167 A f'' _70064 _70065 _70066) (@lem5435126 A _70065 _70064 _70066 i'' j'' f'' h1)). Qed.
Lemma lem5435174 {A : Type'} (_70064 : A -> Prop) (_70065 : nat) (_70066 : nat) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1948 A f'' _70064 _70065 _70066.
Proof. exact (@lem5435173 A _70064 _70065 _70066 i'' j'' f'' h1). Qed.
Lemma lem5435175 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1952 A i''' j''' f'' s.
Proof. exact (@lem5435174 A s (term1953 A i''' f'' s) (term1953 A j''' f'' s) i'' j'' f'' h1). Qed.
Lemma lem5435178 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : (term1953 A i''' f'' s) = (term1953 A j''' f'' s).
Proof. exact (@lem5435175 A i''' j''' s i'' j'' f'' h2 (@lem5435171 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435179 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1954 A i''' j''' f'' s.
Proof. exact (fun h0 : term1955 A i''' j''' f'' s => @lem5435178 A i'' j'' f'' i''' j''' s h1 h2 h3). Qed.
Lemma lem5435181 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435182 {A : Type'} (i''' : type984 A) (j''' : type984 A) (f'' : type681 A) (s : A -> Prop) : (term1954 A i''' j''' f'' s) = ((term1953 A i''' f'' s) = (term1953 A j''' f'' s)).
Proof. exact (@lem5435181 ((term1953 A i''' f'' s) = (term1953 A j''' f'' s))). Qed.
Lemma lem5435183 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : (term1953 A i''' f'' s) = (term1953 A j''' f'' s).
Proof. exact (EQ_MP (@lem5435182 A i''' j''' f'' s) (@lem5435179 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435185 (_70060 : nat) (_70061 : nat) (h1 : term105) : term1585 _70060 _70061.
Proof. exact (EQ_MP (@lem5432577 _70060 _70061) (@lem5432576 _70060 _70061 h1)). Qed.
Lemma lem5435186 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (@lem5435185 term1592 (@I ((A -> Prop) -> nat) (@CARD A) s) h1). Qed.
Lemma lem5435187 {A : Type'} (s : A -> Prop) (h1 : term105) : term1872 A s.
Proof. exact (fun h0 : term1873 A s => @lem5435186 A s h1). Qed.
Lemma lem5435189 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435190 {A : Type'} (s : A -> Prop) : (term1872 A s) = (term1871 A s).
Proof. exact (@lem5435189 (term1871 A s)). Qed.
Lemma lem5435191 {A : Type'} (s : A -> Prop) (h1 : term105) : term1871 A s.
Proof. exact (EQ_MP (@lem5435190 A s) (@lem5435187 A s h1)). Qed.
Lemma lem5435193 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (proj1 (@lem5430665 A i''' j''' s h1)). Qed.
Lemma lem5435194 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1869 A s.
Proof. exact (fun h0 : term1638 A s => @lem5435193 A i''' j''' s h1). Qed.
Lemma lem5435196 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435197 {A : Type'} (s : A -> Prop) : (term1869 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem5435196 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem5435198 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem5435197 A s) (@lem5435194 A i''' j''' s h1)). Qed.
Lemma lem5435200 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (EQ_MP (@lem5434628 A f'' _70064) (@lem5434617 A _70064 i'' j'' f'' h1)). Qed.
Lemma lem5435201 {A : Type'} (_70064 : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' _70064.
Proof. exact (@lem5435200 A _70064 i'' j'' f'' h1). Qed.
Lemma lem5435202 {A : Type'} (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term887 A i'' j'' f'') : term1883 A f'' s.
Proof. exact (@lem5435201 A s i'' j'' f'' h1). Qed.
Lemma lem5435205 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (@lem5435202 A s i'' j'' f'' h1 (@lem5435198 A i''' j''' s h2)). Qed.
Lemma lem5435206 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : term1884 A f'' s.
Proof. exact (fun h0 : term1885 A f'' s => @lem5435205 A i'' j'' f'' i''' j''' s h1 h2). Qed.
Lemma lem5435208 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435209 {A : Type'} (f'' : type681 A) (s : A -> Prop) : (term1884 A f'' s) = (s = (term1606 A f'' s)).
Proof. exact (@lem5435208 (s = (term1606 A f'' s))). Qed.
Lemma lem5435210 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term887 A i'' j'' f'') (h2 : term1751 A i''' j''' s) : s = (term1606 A f'' s).
Proof. exact (EQ_MP (@lem5435209 A f'' s) (@lem5435206 A i'' j'' f'' i''' j''' s h1 h2)). Qed.
Lemma lem5435212 (a : Prop) (b : Prop) : (term1956 a b) = (term1957 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5435213 {A : Type'} (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1713 A s _70078 _70077) = (term1958 A s _70078 _70077).
Proof. exact (@lem5435212 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70077) (s = (term1573 A _70078 _70077))). Qed.
Lemma lem5435214 {A : Type'} (i''' : type984 A) (j''' : type984 A) (_70077 : nat -> Prop) (_70078 : nat -> A) : (term1959 A i''' j''' _70077 _70078) = (term1959 A i''' j''' _70077 _70078).
Proof. exact (eq_refl (term1959 A i''' j''' _70077 _70078)). Qed.
Lemma lem5435215 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1831 A i''' j''' s _70078 _70077) = (term1960 A i''' j''' s _70078 _70077).
Proof. exact (MK_COMB (@lem5435214 A i''' j''' _70077 _70078) (@lem5435213 A s _70078 _70077)). Qed.
Lemma lem5435217 (a : Prop) (b : Prop) : (term1956 a b) = (term1957 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5435218 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1960 A i''' j''' s _70078 _70077) = (term1961 A i''' j''' s _70078 _70077).
Proof. exact (@lem5435217 ((term1714 A i''' _70077 _70078) = (term1714 A j''' _70077 _70078)) (term1690 A s _70078 _70077)). Qed.
Lemma lem5435219 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1831 A i''' j''' s _70078 _70077) = (term1961 A i''' j''' s _70078 _70077).
Proof. exact (TRANS (@lem5435215 A i''' j''' s _70078 _70077) (@lem5435218 A i''' j''' s _70078 _70077)). Qed.
Lemma lem5435221 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5435222 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1961 A i''' j''' s _70078 _70077) = (term1962 A i''' j''' s _70078 _70077).
Proof. exact (@lem5435221 (term1963 A i''' j''' s _70078 _70077)). Qed.
Lemma lem5435223 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (_70078 : nat -> A) (_70077 : nat -> Prop) : (term1831 A i''' j''' s _70078 _70077) = (term1962 A i''' j''' s _70078 _70077).
Proof. exact (TRANS (@lem5435219 A i''' j''' s _70078 _70077) (@lem5435222 A i''' j''' s _70078 _70077)). Qed.
Lemma lem5435225 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1897 A f'' s.
Proof. exact (conj (@lem5435191 A s h1) (@lem5435210 A i'' j'' f'' i''' j''' s h2 h3)). Qed.
Lemma lem5435226 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1964 A i''' j''' f'' s.
Proof. exact (conj (@lem5435183 A i'' j'' f'' i''' j''' s h1 h2 h3) (@lem5435225 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435228 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1962 A i''' j''' s _70078 _70077.
Proof. exact (EQ_MP (@lem5435223 A i''' j''' s _70078 _70077) (@lem5432862 A _70078 _70077 i''' j''' s h1)). Qed.
Lemma lem5435229 {A : Type'} (_70078 : nat -> A) (_70077 : nat -> Prop) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1962 A i''' j''' s _70078 _70077.
Proof. exact (@lem5435228 A _70078 _70077 i''' j''' s h1). Qed.
Lemma lem5435230 {A : Type'} (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term1751 A i''' j''' s) : term1965 A i''' j''' f'' s.
Proof. exact (@lem5435229 A (@I ((A -> Prop) -> nat -> A) f'' s) (term1599 A s) i''' j''' s h1). Qed.
Lemma lem5435233 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : False.
Proof. exact (@lem5435230 A f'' i''' j''' s h3 (@lem5435226 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435234 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : term1966.
Proof. exact (fun h0 : ~ False => @lem5435233 A i'' j'' f'' i''' j''' s h1 h2 h3). Qed.
Lemma lem5435236 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435237 : term1966 = False.
Proof. exact (@lem5435236 False). Qed.
Lemma lem5435238 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (h1 : term105) (h2 : term887 A i'' j'' f'') (h3 : term1751 A i''' j''' s) : False.
Proof. exact (EQ_MP (@lem5435237) (@lem5435234 A i'' j'' f'' i''' j''' s h1 h2 h3)). Qed.
Lemma lem5435958 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : @I ((nat -> Prop) -> Prop) (@FINITE nat) k.
Proof. exact (proj1 (@lem5430671 A s f''' k h1)). Qed.
Lemma lem5435959 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1967 k.
Proof. exact (fun h0 : term1576 k => @lem5435958 A s f''' k h1). Qed.
Lemma lem5435961 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5435962 (k : nat -> Prop) : (term1967 k) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) k).
Proof. exact (@lem5435961 (@I ((nat -> Prop) -> Prop) (@FINITE nat) k)). Qed.
Lemma lem5435963 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : @I ((nat -> Prop) -> Prop) (@FINITE nat) k.
Proof. exact (EQ_MP (@lem5435962 k) (@lem5435959 A s f''' k h1)). Qed.
Lemma lem5435969 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5435970 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1578 A _70089 _70090) = (term1968 A _70089 _70090).
Proof. exact (@lem5435969 (term1575 A _70089 _70090) (term1576 _70090)). Qed.
Lemma lem5435976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5435977 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1969 A _70089 _70090) = (term1970 A _70089 _70090).
Proof. exact (MK_COMB (@lem5435976) (@lem5435970 A _70089 _70090)). Qed.
Lemma lem5435983 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1968 A _70089 _70090) = (term1968 A _70089 _70090).
Proof. exact (eq_refl (term1968 A _70089 _70090)). Qed.
Lemma lem5435984 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : ((term1578 A _70089 _70090) = (term1968 A _70089 _70090)) = ((term1968 A _70089 _70090) = (term1968 A _70089 _70090)).
Proof. exact (MK_COMB (@lem5435977 A _70089 _70090) (@lem5435983 A _70089 _70090)). Qed.
Lemma lem5435986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5435987 (x : Prop) : (x = x) = True.
Proof. exact (@lem5435986 Prop x). Qed.
Lemma lem5435988 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : ((term1968 A _70089 _70090) = (term1968 A _70089 _70090)) = True.
Proof. exact (@lem5435987 (term1968 A _70089 _70090)). Qed.
Lemma lem5435989 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : ((term1578 A _70089 _70090) = (term1968 A _70089 _70090)) = True.
Proof. exact (TRANS (@lem5435984 A _70089 _70090) (@lem5435988 A _70089 _70090)). Qed.
Lemma lem5435990 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : True = ((term1578 A _70089 _70090) = (term1968 A _70089 _70090)).
Proof. exact (SYM (@lem5435989 A _70089 _70090)). Qed.
Lemma lem5435991 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1578 A _70089 _70090) = (term1968 A _70089 _70090).
Proof. exact (EQ_MP (@lem5435990 A _70089 _70090) (@lem0)). Qed.
Lemma lem5435992 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) (h1 : term15 A) : term1968 A _70089 _70090.
Proof. exact (EQ_MP (@lem5435991 A _70089 _70090) (@lem5433478 A _70089 _70090 h1)). Qed.
Lemma lem5435994 (b : Prop) (a : Prop) : (a \/ b) = (term1877 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5435995 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1968 A _70089 _70090) = (term1971 A _70089 _70090).
Proof. exact (@lem5435994 (term1576 _70090) (term1575 A _70089 _70090)). Qed.
Lemma lem5435997 (a : Prop) : (term1879 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5435998 (_70090 : nat -> Prop) : (term1891 _70090) = (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70090).
Proof. exact (@lem5435997 (@I ((nat -> Prop) -> Prop) (@FINITE nat) _70090)). Qed.
Lemma lem5435999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5436000 (_70090 : nat -> Prop) : (term1972 _70090) = (term1973 _70090).
Proof. exact (MK_COMB (@lem5435999) (@lem5435998 _70090)). Qed.
Lemma lem5436001 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1575 A _70089 _70090) = (term1575 A _70089 _70090).
Proof. exact (eq_refl (term1575 A _70089 _70090)). Qed.
Lemma lem5436002 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1971 A _70089 _70090) = (term1974 A _70089 _70090).
Proof. exact (MK_COMB (@lem5436000 _70090) (@lem5436001 A _70089 _70090)). Qed.
Lemma lem5436003 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) : (term1968 A _70089 _70090) = (term1974 A _70089 _70090).
Proof. exact (TRANS (@lem5435995 A _70089 _70090) (@lem5436002 A _70089 _70090)). Qed.
Lemma lem5436006 {A : Type'} (_70089 : nat -> A) (_70090 : nat -> Prop) (h1 : term15 A) : term1974 A _70089 _70090.
Proof. exact (EQ_MP (@lem5436003 A _70089 _70090) (@lem5435992 A _70089 _70090 h1)). Qed.
Lemma lem5436007 {A : Type'} (_70089 : nat -> A) (k : nat -> Prop) (h1 : term15 A) : term1974 A _70089 k.
Proof. exact (@lem5436006 A _70089 k h1). Qed.
Lemma lem5436010 {A : Type'} (_70089 : nat -> A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1575 A _70089 k.
Proof. exact (@lem5436007 A _70089 k h1 (@lem5435963 A s f''' k h2)). Qed.
Lemma lem5436011 {A : Type'} (_70089 : nat -> A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1575 A _70089 k.
Proof. exact (@lem5436010 A _70089 s f''' k h1 h2). Qed.
Lemma lem5436012 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1575 A f''' k.
Proof. exact (@lem5436011 A f''' s f''' k h1 h2). Qed.
Lemma lem5436013 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1975 A f''' k.
Proof. exact (fun h0 : term1866 A f''' k => @lem5436012 A s f''' k h1 h2). Qed.
Lemma lem5436015 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5436016 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (term1975 A f''' k) = (term1575 A f''' k).
Proof. exact (@lem5436015 (term1575 A f''' k)). Qed.
Lemma lem5436017 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1575 A f''' k.
Proof. exact (EQ_MP (@lem5436016 A f''' k) (@lem5436013 A s f''' k h1 h2)). Qed.
Lemma lem5436020 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5436022 {A : Type'} (f''' : nat -> A) (k : nat -> Prop) : (term1866 A f''' k) = (term1976 A f''' k).
Proof. exact (@lem5436020 (term1575 A f''' k)). Qed.
Lemma lem5436025 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term1710 A s f''' k) : term1976 A f''' k.
Proof. exact (EQ_MP (@lem5436022 A f''' k) (@lem5433547 A s f''' k h1)). Qed.
Lemma lem5436028 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : False.
Proof. exact (@lem5436025 A s f''' k h2 (@lem5436017 A s f''' k h1 h2)). Qed.
Lemma lem5436029 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : term1966.
Proof. exact (fun h0 : ~ False => @lem5436028 A s f''' k h1 h2). Qed.
Lemma lem5436031 (p : Prop) : (term1870 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5436032 : term1966 = False.
Proof. exact (@lem5436031 False). Qed.
Lemma lem5436034 {A : Type'} (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term1710 A s f''' k) : False.
Proof. exact (EQ_MP (@lem5436032) (@lem5436029 A s f''' k h1 h2)). Qed.
Lemma lem5436035 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (f''' : nat -> A) (k : nat -> Prop) (h1 : term15 A) (h2 : term105) (h3 : term887 A i'' j'' f'') (h4 : term541 A i''' j''' s f''' k) : False.
Proof. exact (or_elim (@lem5430658 A i''' j''' s f''' k h4) (fun h0 : term1751 A i''' j''' s => @lem5435238 A i'' j'' f'' i''' j''' s h2 h3 h0) (fun h0 : term1710 A s f''' k => @lem5436034 A s f''' k h1 h0)). Qed.
Lemma lem5436036 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (k : nat -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term15 A) (h2 : term105) (h3 : term544 A i''' j''' s k) (h4 : term887 A i'' j'' f'') : False.
Proof. exact (ex_elim (@lem5428144 A i''' j''' s k h3) (fun f''' : nat -> A => fun h0 : term543 A i''' j''' s k f''' => @lem5436035 A i'' j'' f'' i''' j''' s f''' k h1 h2 h4 h0)). Qed.
Lemma lem5436037 {A : Type'} (i''' : type984 A) (j''' : type984 A) (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term15 A) (h2 : term105) (h3 : term546 A i''' j''' s) (h4 : term887 A i'' j'' f'') : False.
Proof. exact (ex_elim (@lem5428143 A i''' j''' s h3) (fun k : nat -> Prop => fun h0 : term545 A i''' j''' s k => @lem5436036 A i''' j''' s k i'' j'' f'' h1 h2 h0 h4)). Qed.
Lemma lem5436038 {A : Type'} (i''' : type984 A) (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term15 A) (h2 : term105) (h3 : term548 A i''' s) (h4 : term887 A i'' j'' f'') : False.
Proof. exact (ex_elim (@lem5428142 A i''' s h3) (fun j''' : type984 A => fun h0 : term547 A i''' s j''' => @lem5436037 A i''' j''' s i'' j'' f'' h1 h2 h0 h4)). Qed.
Lemma lem5436039 {A : Type'} (s : A -> Prop) (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term15 A) (h2 : term105) (h3 : term550 A s) (h4 : term887 A i'' j'' f'') : False.
Proof. exact (ex_elim (@lem5428141 A s h3) (fun i''' : type984 A => fun h0 : term549 A s i''' => @lem5436038 A i''' s i'' j'' f'' h1 h2 h0 h4)). Qed.
Lemma lem5436040 {A : Type'} (i'' : type661 A) (j'' : type661 A) (f'' : type681 A) (h1 : term15 A) (h2 : term105) (h3 : term10 A) (h4 : term887 A i'' j'' f'') : False.
Proof. exact (ex_elim (@lem5425159 A h3) (fun s : A -> Prop => fun h0 : term551 A s => @lem5436039 A s i'' j'' f'' h1 h2 h0 h4)). Qed.
Lemma lem5436041 {A : Type'} (i'' : type661 A) (j'' : type661 A) (h1 : term15 A) (h2 : term105) (h3 : term890 A i'' j'') (h4 : term10 A) : False.
Proof. exact (ex_elim (@lem5428139 A i'' j'' h3) (fun f'' : type681 A => fun h0 : term889 A i'' j'' f'' => @lem5436040 A i'' j'' f'' h1 h2 h4 h0)). Qed.
Lemma lem5436042 {A : Type'} (i'' : type661 A) (h1 : term15 A) (h2 : term105) (h3 : term892 A i'') (h4 : term10 A) : False.
Proof. exact (ex_elim (@lem5428138 A i'' h3) (fun j'' : type661 A => fun h0 : term891 A i'' j'' => @lem5436041 A i'' j'' h1 h2 h0 h4)). Qed.
Lemma lem5436043 {A : Type'} (h1 : term11 A) (h2 : term15 A) (h3 : term105) (h4 : term10 A) : False.
Proof. exact (ex_elim (@lem5426583 A h1) (fun i'' : type661 A => fun h0 : term893 A i'' => @lem5436042 A i'' h2 h3 h0 h4)). Qed.
Lemma lem5436044 {A : Type'} (i' : type177 A) (j' : type177 A) (h1 : term11 A) (h2 : term15 A) (h3 : term105) (h4 : term1229 A i' j') (h5 : term10 A) : False.
Proof. exact (ex_elim (@lem5428136 A i' j' h4) (fun f' : type179 A => fun h0 : term1228 A i' j' f' => @lem5436043 A h1 h2 h3 h5)). Qed.
Lemma lem5436045 {A : Type'} (i' : type177 A) (h1 : term11 A) (h2 : term15 A) (h3 : term105) (h4 : term1231 A i') (h5 : term10 A) : False.
Proof. exact (ex_elim (@lem5428135 A i' h4) (fun j' : type177 A => fun h0 : term1230 A i' j' => @lem5436044 A i' j' h1 h2 h3 h0 h5)). Qed.
Lemma lem5436046 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term105) (h5 : term10 A) : False.
Proof. exact (ex_elim (@lem5427357 A h2) (fun i' : type177 A => fun h0 : term1232 A i' => @lem5436045 A i' h1 h3 h4 h0 h5)). Qed.
Lemma lem5436047 {A : Type'} (i : type987) (j : type987) (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term105) (h5 : term1568 i j) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem5428133 i j h5) (fun f : type992 => fun h0 : term1567 i j f => @lem5436046 A h1 h2 h3 h4 h6)). Qed.
Lemma lem5436048 {A : Type'} (i : type987) (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term105) (h5 : term1570 i) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem5428132 i h5) (fun j : type987 => fun h0 : term1569 i j => @lem5436047 A i j h1 h2 h3 h4 h0 h6)). Qed.
Lemma lem5436049 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term12) (h5 : term105) (h6 : term10 A) : False.
Proof. exact (ex_elim (@lem5428131 h4) (fun i : type987 => fun h0 : term1571 i => @lem5436048 A i h1 h2 h3 h5 h0 h6)). Qed.
Lemma lem5436050 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term12) (h5 : term105) (h6 : term10 A) : term105 = False.
Proof. exact (prop_ext (fun h7 : term105 => @lem5436049 A h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5425809 h5)). Qed.
Lemma lem5436051 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term12) (h5 : term105) (h6 : term10 A) : False.
Proof. exact (EQ_MP (@lem5436050 A h1 h2 h3 h4 h5 h6) (@lem5425809 h5)). Qed.
Lemma lem5436052 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term105) (h5 : term10 A) : term26.
Proof. exact (fun h0 : term12 => @lem5436051 A h1 h2 h3 h0 h4 h5). Qed.
Lemma lem5436053 : term26 = term27.
Proof. exact (@lem69 term12). Qed.
Lemma lem5436054 {A : Type'} (h1 : term11 A) (h2 : term13 A) (h3 : term15 A) (h4 : term105) (h5 : term10 A) : term27.
Proof. exact (EQ_MP (@lem5436053) (@lem5436052 A h1 h2 h3 h4 h5)). Qed.
Lemma lem5436055 {A : Type'} (h1 : term11 A) (h2 : term15 A) (h3 : term105) (h4 : term10 A) : term30 A.
Proof. exact (fun h0 : term13 A => @lem5436054 A h1 h0 h2 h3 h4). Qed.
Lemma lem5436056 {A : Type'} (h1 : term15 A) (h2 : term105) (h3 : term10 A) : term33 A.
Proof. exact (fun h0 : term11 A => @lem5436055 A h0 h1 h2 h3). Qed.
Lemma lem5436057 {A : Type'} (h1 : term15 A) (h2 : term10 A) : term36 A.
Proof. exact (fun h0 : term105 => @lem5436056 A h1 h0 h2). Qed.
Lemma lem5436058 {A : Type'} (h1 : term15 A) (h2 : term10 A) : term39 A.
Proof. exact (fun h0 : term20 => @lem5436057 A h1 h2). Qed.
Lemma lem5436059 {A : Type'} (h1 : term15 A) (h2 : term10 A) : term42 A.
Proof. exact (fun h0 : term21 A => @lem5436058 A h1 h2). Qed.
Lemma lem5436060 {A B : Type'} (h1 : term15 A) (h2 : term10 A) : term45 A B.
Proof. exact (fun h0 : term15 B => @lem5436059 A h1 h2). Qed.
Lemma lem5436061 {A B : Type'} (h1 : term10 A) : term47 A B.
Proof. exact (fun h0 : term15 A => @lem5436060 A B h0 h1). Qed.
Lemma lem5436062 {A B : Type'} (h1 : term10 A) : term50 A B.
Proof. exact (fun h0 : term16 A B => @lem5436061 A B h1). Qed.
Lemma lem5436063 {A B : Type'} (h1 : term10 A) : term53 A B.
Proof. exact (fun h0 : term18 A => @lem5436062 A B h1). Qed.
Lemma lem5436064 {A B : Type'} (h1 : term10 A) : term56 A B.
Proof. exact (fun h0 : term19 A => @lem5436063 A B h1). Qed.
Lemma lem5436065 {A B : Type'} (h1 : term10 A) : term59 A B.
Proof. exact (fun h0 : term14 A B => @lem5436064 A B h1). Qed.
Lemma lem5436066 {A B : Type'} (h1 : term10 A) : term62 A B.
Proof. exact (fun h0 : term17 A => @lem5436065 A B h1). Qed.
Lemma lem5436067 {A B : Type'} : term64 A B.
Proof. exact (fun h0 : term10 A => @lem5436066 A B h0). Qed.
Lemma lem5436068 {A B : Type'} : term22 A B.
Proof. exact (EQ_MP (@lem5424278 A B) (@lem5436067 A B)). Qed.
Lemma lem5436070 {A B : Type'} : term22 A B.
Proof. exact (@lem5423225 A B (@lem5436068 A B)). Qed.
Lemma lem5436071 {A B : Type'} (h1 : term10 A) : term61 A B.
Proof. exact (@lem5436070 A B (@lem5423193 A h1)). Qed.
Lemma lem5436072 {A B : Type'} (h1 : term10 A) : term58 A B.
Proof. exact (@lem5436071 A B h1 (@lem5423204 A)). Qed.
Lemma lem5436073 {A B : Type'} (h1 : term10 A) : term55 A B.
Proof. exact (@lem5436072 A B h1 (@lem5423201 A B)). Qed.
Lemma lem5436074 {A B : Type'} (h1 : term10 A) : term52 A B.
Proof. exact (@lem5436073 A B h1 (@lem5423206 A)). Qed.
Lemma lem5436075 {A B : Type'} (h1 : term10 A) : term49 A B.
Proof. exact (@lem5436074 A B h1 (@lem5423205 A)). Qed.
Lemma lem5436076 {A B : Type'} (h1 : term10 A) : term46 A B.
Proof. exact (@lem5436075 A B h1 (@lem5423203 A B)). Qed.
Lemma lem5436077 {A B : Type'} (h1 : term10 A) : term44 A B.
Proof. exact (@lem5436076 A B h1 (@lem5423207 A)). Qed.
Lemma lem5436078 {A : Type'} (h1 : term10 A) : term41 A.
Proof. exact (@lem5436077 A Prop h1 (@lem5423202 Prop)). Qed.
Lemma lem5436079 {A : Type'} (h1 : term10 A) : term38 A.
Proof. exact (@lem5436078 A h1 (@lem5423209 A)). Qed.
Lemma lem5436080 {A : Type'} (h1 : term10 A) : term35 A.
Proof. exact (@lem5436079 A h1 (@lem5423208)). Qed.
Lemma lem5436081 {A : Type'} (h1 : term10 A) : term32 A.
Proof. exact (@lem5436080 A h1 (@lem5329299)). Qed.
Lemma lem5436082 {A : Type'} (h1 : term10 A) : term29 A.
Proof. exact (@lem5436081 A h1 (@lem5423194 A)). Qed.
Lemma lem5436083 {A : Type'} (h1 : term10 A) : term26.
Proof. exact (@lem5436082 A h1 (@lem5423198 A)). Qed.
Lemma lem5436084 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem5436083 A h1 (@lem5423195)). Qed.
Lemma lem5436085 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem5436084 A h1) (fun h2 : False => @lem5423193 A h1)). Qed.
Lemma lem5436086 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem5436085 A h1) (@lem5423193 A h1)). Qed.
Lemma lem5436087 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem5436086 A h0). Qed.
Lemma lem5436088 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem5423192 A) (@lem5436087 A)). Qed.
