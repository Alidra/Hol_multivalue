Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIVISION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2387577_spec.
Require Import thm69_spec.
Lemma lem2387589 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2387590 : term1 = term2.
Proof. exact (@lem2387589 term1). Qed.
Lemma lem2387591 : term2 = term1.
Proof. exact (SYM (@lem2387590)). Qed.
Lemma lem2387592 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2387595 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2387596 : term5.
Proof. exact (fun h0 : term4 => @lem2387595 h0). Qed.
Lemma lem2387597 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2387598 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2387599 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2387597 h2 (@lem2387598 h1)). Qed.
Lemma lem2387600 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2387599 h1 h0). Qed.
Lemma lem2387601 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2387602 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2387600 h1 (@lem2387601 h2)). Qed.
Lemma lem2387603 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2387602 h0 h1). Qed.
Lemma lem2387604 : term7.
Proof. exact (fun h0 : term5 => @lem2387603 h0). Qed.
Lemma lem2387607 : term5.
Proof. exact (@lem2387604 (@lem2387596)). Qed.
Lemma lem2387625 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2387626 : term8 = term9.
Proof. exact (@lem2387625 term10). Qed.
Lemma lem2387641 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2387648 : term4 = term12.
Proof. exact (MK_COMB (@lem2387641) (@lem2387626)). Qed.
Lemma lem2387652 (n : int) (h1 : (n = term13) = False) : (n = term13) = False.
Proof. exact (h1). Qed.
Lemma lem2387653 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem2387654 (n : int) (h1 : (n = term13) = False) : (term14 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem2387653) (@lem2387652 n h1)). Qed.
Lemma lem2387661 (n : int) (m : int) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem2387662 (m : int) (n : int) (h1 : (n = term13) = False) : (term16 n m) = (term17 n m).
Proof. exact (MK_COMB (@lem2387654 n h1) (@lem2387661 n m)). Qed.
Lemma lem2387669 (m : int) (n : int) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2387670 (m : int) (n : int) (h1 : (n = term13) = False) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem2387662 m n h1) (@lem2387669 m n)). Qed.
Lemma lem2387672 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2387673 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem2387672 Prop t1 t2). Qed.
Lemma lem2387674 (m : int) (n : int) : (term20 m n) = (term18 m n).
Proof. exact (@lem2387673 (term15 n m) (term18 m n)). Qed.
Lemma lem2387677 (m : int) (n : int) (h1 : (n = term13) = False) : (term19 m n) = (term18 m n).
Proof. exact (TRANS (@lem2387670 m n h1) (@lem2387674 m n)). Qed.
Lemma lem2387678 (m : int) (n : int) : term21 m n.
Proof. exact (fun h0 : (n = term13) = False => @lem2387677 m n h0). Qed.
Lemma lem2387680 (n : int) (h1 : (n = term13) = True) : (n = term13) = True.
Proof. exact (h1). Qed.
Lemma lem2387681 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem2387682 (n : int) (h1 : (n = term13) = True) : (term14 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem2387681) (@lem2387680 n h1)). Qed.
Lemma lem2387689 (n : int) (m : int) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem2387690 (m : int) (n : int) (h1 : (n = term13) = True) : (term16 n m) = (term22 n m).
Proof. exact (MK_COMB (@lem2387682 n h1) (@lem2387689 n m)). Qed.
Lemma lem2387697 (m : int) (n : int) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2387698 (m : int) (n : int) (h1 : (n = term13) = True) : (term19 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem2387690 m n h1) (@lem2387697 m n)). Qed.
Lemma lem2387700 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2387701 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem2387700 Prop t2 t1). Qed.
Lemma lem2387702 (n : int) (m : int) : (term23 m n) = (term15 n m).
Proof. exact (@lem2387701 (term18 m n) (term15 n m)). Qed.
Lemma lem2387705 (m : int) (n : int) (h1 : (n = term13) = True) : (term19 m n) = (term15 n m).
Proof. exact (TRANS (@lem2387698 m n h1) (@lem2387702 n m)). Qed.
Lemma lem2387706 (n : int) (m : int) : term24 n m.
Proof. exact (fun h0 : (n = term13) = True => @lem2387705 m n h0). Qed.
Lemma lem2387707 (n : int) (m : int) : term25 n m.
Proof. exact (conj (@lem2387678 m n) (@lem2387706 n m)). Qed.
Lemma lem2387709 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term26 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem2387710 (m : int) (n : int) : term27 m n.
Proof. exact (@lem2387709 (term19 m n) (term15 n m) (n = term13) (term18 m n)). Qed.
Lemma lem2387755 (m : int) (n : int) : (term19 m n) = (term28 m n).
Proof. exact (@lem2387710 m n (@lem2387707 n m)). Qed.
Lemma lem2387756 (m : int) : (term29 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2387755 m n)). Qed.
Lemma lem2387757 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387758 (m : int) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem2387757) (@lem2387756 m)). Qed.
Lemma lem2387759 : term33 = term34.
Proof. exact (fun_ext (fun m : int => @lem2387758 m)). Qed.
Lemma lem2387760 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387761 : term10 = term35.
Proof. exact (MK_COMB (@lem2387760) (@lem2387759)). Qed.
Lemma lem2387762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2387763 : term9 = term36.
Proof. exact (MK_COMB (@lem2387762) (@lem2387761)). Qed.
Lemma lem2387778 (m : int) (n : int) : (term37 m n) = (term37 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem2387779 (m : int) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : int => @lem2387778 m n)). Qed.
Lemma lem2387780 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387781 (m : int) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem2387780) (@lem2387779 m)). Qed.
Lemma lem2387782 : term40 = term40.
Proof. exact (fun_ext (fun m : int => @lem2387781 m)). Qed.
Lemma lem2387783 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387784 : term1 = term1.
Proof. exact (MK_COMB (@lem2387783) (@lem2387782)). Qed.
Lemma lem2387785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2387786 : term3 = term3.
Proof. exact (MK_COMB (@lem2387785) (@lem2387784)). Qed.
Lemma lem2387787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2387788 : term11 = term11.
Proof. exact (MK_COMB (@lem2387787) (@lem2387786)). Qed.
Lemma lem2387789 : term12 = term41.
Proof. exact (MK_COMB (@lem2387788) (@lem2387763)). Qed.
Lemma lem2387836 : term4 = term41.
Proof. exact (TRANS (@lem2387648) (@lem2387789)). Qed.
Lemma lem2387837 : term41 = term4.
Proof. exact (SYM (@lem2387836)). Qed.
Lemma lem2387838 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2387839 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem2387848 (m : int) (n : int) : (term42 m n) = (term43 m n).
Proof. exact (@lem17045 (term44 m n) (term45 m n)). Qed.
Lemma lem2387850 (m : int) (n : int) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem2387851 (m : int) (n : int) : (term47 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem2387850 m n) (@lem2387848 m n)). Qed.
Lemma lem2387852 (m : int) (n : int) : (term49 m n) = (term47 m n).
Proof. exact (@lem17045 (m = (term50 m n)) (term51 m n)). Qed.
Lemma lem2387853 (m : int) (n : int) : (term49 m n) = (term48 m n).
Proof. exact (TRANS (@lem2387852 m n) (@lem2387851 m n)). Qed.
Lemma lem2387855 (n : int) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2387856 (m : int) (n : int) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem2387855 n) (@lem2387853 m n)). Qed.
Lemma lem2387857 (m : int) (n : int) : (term55 m n) = (term53 m n).
Proof. exact (@lem17362 (term56 n) (term57 m n)). Qed.
Lemma lem2387858 (m : int) (n : int) : (term55 m n) = (term54 m n).
Proof. exact (TRANS (@lem2387857 m n) (@lem2387856 m n)). Qed.
Lemma lem2387859 (P : int -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2387860 (m : int) : (term60 m) = (term61 m).
Proof. exact (@lem2387859 (term38 m)). Qed.
Lemma lem2387861 (m : int) (n : int) : (term62 m n) = (term37 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem2387862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2387863 (m : int) (n : int) : (term63 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem2387862) (@lem2387861 m n)). Qed.
Lemma lem2387864 (m : int) (n : int) : (term63 m n) = (term54 m n).
Proof. exact (TRANS (@lem2387863 m n) (@lem2387858 m n)). Qed.
Lemma lem2387865 (m : int) : (term64 m) = (term65 m).
Proof. exact (fun_ext (fun n : int => @lem2387864 m n)). Qed.
Lemma lem2387866 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2387867 (m : int) : (term61 m) = (term66 m).
Proof. exact (MK_COMB (@lem2387866) (@lem2387865 m)). Qed.
Lemma lem2387868 (m : int) : (term60 m) = (term66 m).
Proof. exact (TRANS (@lem2387860 m) (@lem2387867 m)). Qed.
Lemma lem2387869 (P : int -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2387870 : term3 = term67.
Proof. exact (@lem2387869 term40). Qed.
Lemma lem2387871 (m : int) : (term68 m) = (term39 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem2387872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2387873 (m : int) : (term69 m) = (term60 m).
Proof. exact (MK_COMB (@lem2387872) (@lem2387871 m)). Qed.
Lemma lem2387874 (m : int) : (term69 m) = (term66 m).
Proof. exact (TRANS (@lem2387873 m) (@lem2387868 m)). Qed.
Lemma lem2387875 : term70 = term71.
Proof. exact (fun_ext (fun m : int => @lem2387874 m)). Qed.
Lemma lem2387876 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2387877 : term67 = term72.
Proof. exact (MK_COMB (@lem2387876) (@lem2387875)). Qed.
Lemma lem2387934 : term3 = term72.
Proof. exact (TRANS (@lem2387870) (@lem2387877)). Qed.
Lemma lem2387935 (h1 : term3) : term72.
Proof. exact (EQ_MP (@lem2387934) (@lem2387838 h1)). Qed.
Lemma lem2387960 (m : int) (n : int) : (term28 m n) = (term28 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem2387961 (m : int) : (term30 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2387960 m n)). Qed.
Lemma lem2387962 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387963 (m : int) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem2387962) (@lem2387961 m)). Qed.
Lemma lem2387964 : term34 = term34.
Proof. exact (fun_ext (fun m : int => @lem2387963 m)). Qed.
Lemma lem2387965 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387966 : term35 = term35.
Proof. exact (MK_COMB (@lem2387965) (@lem2387964)). Qed.
Lemma lem2387972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2387973 (P : int -> Prop) (Q : int -> Prop) : (term75 P Q) = (term76 P Q).
Proof. exact (@lem2387972 int P Q). Qed.
Lemma lem2387974 (m : int) : (term77 m) = (term78 m).
Proof. exact (@lem2387973 (term79 m) (term80 m)). Qed.
Lemma lem2387975 (n : int) (m : int) : (term81 m n) = (term82 n m).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem2387976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2387977 (n : int) (m : int) : (term83 m n) = (term84 n m).
Proof. exact (MK_COMB (@lem2387976) (@lem2387975 n m)). Qed.
Lemma lem2387978 (m : int) (n : int) : (term85 m n) = (term86 m n).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem2387979 (m : int) (n : int) : (term87 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem2387977 n m) (@lem2387978 m n)). Qed.
Lemma lem2387980 (m : int) : (term88 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2387979 m n)). Qed.
Lemma lem2387981 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387982 (m : int) : (term77 m) = (term32 m).
Proof. exact (MK_COMB (@lem2387981) (@lem2387980 m)). Qed.
Lemma lem2387983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2387984 (m : int) : (term89 m) = (term90 m).
Proof. exact (MK_COMB (@lem2387983) (@lem2387982 m)). Qed.
Lemma lem2387985 (n : int) (m : int) : (term81 m n) = (term82 n m).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem2387986 (m : int) : (term91 m) = (term79 m).
Proof. exact (fun_ext (fun n : int => @lem2387985 n m)). Qed.
Lemma lem2387987 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387988 (m : int) : (term92 m) = (term93 m).
Proof. exact (MK_COMB (@lem2387987) (@lem2387986 m)). Qed.
Lemma lem2387989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2387990 (m : int) : (term94 m) = (term95 m).
Proof. exact (MK_COMB (@lem2387989) (@lem2387988 m)). Qed.
Lemma lem2387991 (m : int) (n : int) : (term85 m n) = (term86 m n).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem2387992 (m : int) : (term96 m) = (term80 m).
Proof. exact (fun_ext (fun n : int => @lem2387991 m n)). Qed.
Lemma lem2387993 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387994 (m : int) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem2387993) (@lem2387992 m)). Qed.
Lemma lem2387995 (m : int) : (term78 m) = (term99 m).
Proof. exact (MK_COMB (@lem2387990 m) (@lem2387994 m)). Qed.
Lemma lem2387996 (m : int) : ((term77 m) = (term78 m)) = ((term32 m) = (term99 m)).
Proof. exact (MK_COMB (@lem2387984 m) (@lem2387995 m)). Qed.
Lemma lem2387997 (m : int) : (term32 m) = (term99 m).
Proof. exact (EQ_MP (@lem2387996 m) (@lem2387974 m)). Qed.
Lemma lem2388094 : term34 = term100.
Proof. exact (fun_ext (fun m : int => @lem2387997 m)). Qed.
Lemma lem2388095 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388096 : term35 = term101.
Proof. exact (MK_COMB (@lem2388095) (@lem2388094)). Qed.
Lemma lem2388098 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2388099 (P : int -> Prop) (Q : int -> Prop) : (term75 P Q) = (term76 P Q).
Proof. exact (@lem2388098 int P Q). Qed.
Lemma lem2388100 : term102 = term103.
Proof. exact (@lem2388099 term104 term105). Qed.
Lemma lem2388101 (m : int) : (term106 m) = (term93 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem2388102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2388103 (m : int) : (term107 m) = (term95 m).
Proof. exact (MK_COMB (@lem2388102) (@lem2388101 m)). Qed.
Lemma lem2388104 (m : int) : (term108 m) = (term98 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem2388105 (m : int) : (term109 m) = (term99 m).
Proof. exact (MK_COMB (@lem2388103 m) (@lem2388104 m)). Qed.
Lemma lem2388106 : term110 = term100.
Proof. exact (fun_ext (fun m : int => @lem2388105 m)). Qed.
Lemma lem2388107 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388108 : term102 = term101.
Proof. exact (MK_COMB (@lem2388107) (@lem2388106)). Qed.
Lemma lem2388109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2388110 : term111 = term112.
Proof. exact (MK_COMB (@lem2388109) (@lem2388108)). Qed.
Lemma lem2388111 (m : int) : (term106 m) = (term93 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem2388112 : term113 = term104.
Proof. exact (fun_ext (fun m : int => @lem2388111 m)). Qed.
Lemma lem2388113 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388114 : term114 = term115.
Proof. exact (MK_COMB (@lem2388113) (@lem2388112)). Qed.
Lemma lem2388115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2388116 : term116 = term117.
Proof. exact (MK_COMB (@lem2388115) (@lem2388114)). Qed.
Lemma lem2388117 (m : int) : (term108 m) = (term98 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem2388118 : term118 = term105.
Proof. exact (fun_ext (fun m : int => @lem2388117 m)). Qed.
Lemma lem2388119 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388120 : term119 = term120.
Proof. exact (MK_COMB (@lem2388119) (@lem2388118)). Qed.
Lemma lem2388121 : term103 = term121.
Proof. exact (MK_COMB (@lem2388116) (@lem2388120)). Qed.
Lemma lem2388122 : (term102 = term103) = (term101 = term121).
Proof. exact (MK_COMB (@lem2388110) (@lem2388121)). Qed.
Lemma lem2388123 : term101 = term121.
Proof. exact (EQ_MP (@lem2388122) (@lem2388100)). Qed.
Lemma lem2388230 : term35 = term121.
Proof. exact (TRANS (@lem2388096) (@lem2388123)). Qed.
Lemma lem2388231 : term35 = term121.
Proof. exact (TRANS (@lem2387966) (@lem2388230)). Qed.
Lemma lem2388232 (h1 : term35) : term121.
Proof. exact (EQ_MP (@lem2388231) (@lem2387839 h1)). Qed.
Lemma lem2388233 (m : int) (h1 : term66 m) : term66 m.
Proof. exact (h1). Qed.
Lemma lem2388297 (m : int) (n : int) : (term86 m n) = (term86 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem2388298 (m : int) : (term80 m) = (term80 m).
Proof. exact (fun_ext (fun n : int => @lem2388297 m n)). Qed.
Lemma lem2388299 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388300 (m : int) : (term98 m) = (term98 m).
Proof. exact (MK_COMB (@lem2388299) (@lem2388298 m)). Qed.
Lemma lem2388301 : term105 = term105.
Proof. exact (fun_ext (fun m : int => @lem2388300 m)). Qed.
Lemma lem2388302 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388303 : term120 = term120.
Proof. exact (MK_COMB (@lem2388302) (@lem2388301)). Qed.
Lemma lem2388342 (n : int) (m : int) : (term82 n m) = (term82 n m).
Proof. exact (eq_refl (term82 n m)). Qed.
Lemma lem2388343 (m : int) : (term79 m) = (term79 m).
Proof. exact (fun_ext (fun n : int => @lem2388342 n m)). Qed.
Lemma lem2388344 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388345 (m : int) : (term93 m) = (term93 m).
Proof. exact (MK_COMB (@lem2388344) (@lem2388343 m)). Qed.
Lemma lem2388346 : term104 = term104.
Proof. exact (fun_ext (fun m : int => @lem2388345 m)). Qed.
Lemma lem2388347 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388348 : term115 = term115.
Proof. exact (MK_COMB (@lem2388347) (@lem2388346)). Qed.
Lemma lem2388349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2388350 : term117 = term117.
Proof. exact (MK_COMB (@lem2388349) (@lem2388348)). Qed.
Lemma lem2388351 : term121 = term121.
Proof. exact (MK_COMB (@lem2388350) (@lem2388303)). Qed.
Lemma lem2388352 (h1 : term35) : term121.
Proof. exact (EQ_MP (@lem2388351) (@lem2388232 h1)). Qed.
Lemma lem2388424 (m : int) (n : int) (h1 : term54 m n) : term54 m n.
Proof. exact (h1). Qed.
Lemma lem2388425 (m : int) (n : int) (h1 : term54 m n) : term48 m n.
Proof. exact (proj2 (@lem2388424 m n h1)). Qed.
Lemma lem2388427 (h1 : term35) : term120.
Proof. exact (proj2 (@lem2388352 h1)). Qed.
Lemma lem2388430 (m : int) (n : int) (h1 : term43 m n) : term43 m n.
Proof. exact (h1). Qed.
Lemma lem2388477 (m : int) (n : int) : (term86 m n) = (term122 m n).
Proof. exact (@lem19490 (term44 m n) (n = term13) (term123 m n)). Qed.
Lemma lem2388484 (m : int) (n : int) : (term124 m n) = (term125 m n).
Proof. exact (@lem19490 (term45 m n) (n = term13) (m = (term50 m n))). Qed.
Lemma lem2388487 (m : int) (n : int) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem2388488 (m : int) (n : int) : (term122 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem2388487 m n) (@lem2388484 m n)). Qed.
Lemma lem2388490 (m : int) (n : int) : (term86 m n) = (term127 m n).
Proof. exact (TRANS (@lem2388477 m n) (@lem2388488 m n)). Qed.
Lemma lem2388491 (m : int) : (term80 m) = (term128 m).
Proof. exact (fun_ext (fun n : int => @lem2388490 m n)). Qed.
Lemma lem2388492 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388493 (m : int) : (term98 m) = (term129 m).
Proof. exact (MK_COMB (@lem2388492) (@lem2388491 m)). Qed.
Lemma lem2388494 : term105 = term130.
Proof. exact (fun_ext (fun m : int => @lem2388493 m)). Qed.
Lemma lem2388495 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388497 : term120 = term131.
Proof. exact (MK_COMB (@lem2388495) (@lem2388494)). Qed.
Lemma lem2388498 (h1 : term35) : term131.
Proof. exact (EQ_MP (@lem2388497) (@lem2388427 h1)). Qed.
Lemma lem2388502 (m : int) (n : int) (h1 : term132 m n) : term132 m n.
Proof. exact (h1). Qed.
Lemma lem2388547 (m : int) (n : int) : (term86 m n) = (term122 m n).
Proof. exact (@lem19490 (term44 m n) (n = term13) (term123 m n)). Qed.
Lemma lem2388554 (m : int) (n : int) : (term124 m n) = (term125 m n).
Proof. exact (@lem19490 (term45 m n) (n = term13) (m = (term50 m n))). Qed.
Lemma lem2388557 (m : int) (n : int) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem2388558 (m : int) (n : int) : (term122 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem2388557 m n) (@lem2388554 m n)). Qed.
Lemma lem2388560 (m : int) (n : int) : (term86 m n) = (term127 m n).
Proof. exact (TRANS (@lem2388547 m n) (@lem2388558 m n)). Qed.
Lemma lem2388561 (m : int) : (term80 m) = (term128 m).
Proof. exact (fun_ext (fun n : int => @lem2388560 m n)). Qed.
Lemma lem2388562 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388563 (m : int) : (term98 m) = (term129 m).
Proof. exact (MK_COMB (@lem2388562) (@lem2388561 m)). Qed.
Lemma lem2388564 : term105 = term130.
Proof. exact (fun_ext (fun m : int => @lem2388563 m)). Qed.
Lemma lem2388565 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388567 : term120 = term131.
Proof. exact (MK_COMB (@lem2388565) (@lem2388564)). Qed.
Lemma lem2388568 (h1 : term35) : term131.
Proof. exact (EQ_MP (@lem2388567) (@lem2388427 h1)). Qed.
Lemma lem2388572 (m : int) (n : int) (h1 : term133 m n) : term133 m n.
Proof. exact (h1). Qed.
Lemma lem2388617 (m : int) (n : int) : (term86 m n) = (term122 m n).
Proof. exact (@lem19490 (term44 m n) (n = term13) (term123 m n)). Qed.
Lemma lem2388624 (m : int) (n : int) : (term124 m n) = (term125 m n).
Proof. exact (@lem19490 (term45 m n) (n = term13) (m = (term50 m n))). Qed.
Lemma lem2388627 (m : int) (n : int) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem2388628 (m : int) (n : int) : (term122 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem2388627 m n) (@lem2388624 m n)). Qed.
Lemma lem2388630 (m : int) (n : int) : (term86 m n) = (term127 m n).
Proof. exact (TRANS (@lem2388617 m n) (@lem2388628 m n)). Qed.
Lemma lem2388631 (m : int) : (term80 m) = (term128 m).
Proof. exact (fun_ext (fun n : int => @lem2388630 m n)). Qed.
Lemma lem2388632 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388633 (m : int) : (term98 m) = (term129 m).
Proof. exact (MK_COMB (@lem2388632) (@lem2388631 m)). Qed.
Lemma lem2388634 : term105 = term130.
Proof. exact (fun_ext (fun m : int => @lem2388633 m)). Qed.
Lemma lem2388635 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2388637 : term120 = term131.
Proof. exact (MK_COMB (@lem2388635) (@lem2388634)). Qed.
Lemma lem2388638 (h1 : term35) : term131.
Proof. exact (EQ_MP (@lem2388637) (@lem2388427 h1)). Qed.
Lemma lem2388642 (m : int) (n : int) (h1 : term134 m n) : term134 m n.
Proof. exact (h1). Qed.
Lemma lem2388649 (_29203 : int) (h1 : term35) : term135 _29203.
Proof. exact (@lem2388498 h1 _29203). Qed.
Lemma lem2388650 (_29203 : int) : (term135 _29203) = (term129 _29203).
Proof. exact (eq_refl (term135 _29203)). Qed.
Lemma lem2388651 (_29203 : int) (h1 : term35) : term129 _29203.
Proof. exact (EQ_MP (@lem2388650 _29203) (@lem2388649 _29203 h1)). Qed.
Lemma lem2388652 (_29203 : int) (_29204 : int) (h1 : term35) : term136 _29203 _29204.
Proof. exact (@lem2388651 _29203 h1 _29204). Qed.
Lemma lem2388653 (_29203 : int) (_29204 : int) : (term136 _29203 _29204) = (term127 _29203 _29204).
Proof. exact (eq_refl (term136 _29203 _29204)). Qed.
Lemma lem2388654 (_29203 : int) (_29204 : int) (h1 : term35) : term127 _29203 _29204.
Proof. exact (EQ_MP (@lem2388653 _29203 _29204) (@lem2388652 _29203 _29204 h1)). Qed.
Lemma lem2388661 (_29207 : int) (h1 : term35) : term135 _29207.
Proof. exact (@lem2388568 h1 _29207). Qed.
Lemma lem2388662 (_29207 : int) : (term135 _29207) = (term129 _29207).
Proof. exact (eq_refl (term135 _29207)). Qed.
Lemma lem2388663 (_29207 : int) (h1 : term35) : term129 _29207.
Proof. exact (EQ_MP (@lem2388662 _29207) (@lem2388661 _29207 h1)). Qed.
Lemma lem2388664 (_29207 : int) (_29208 : int) (h1 : term35) : term136 _29207 _29208.
Proof. exact (@lem2388663 _29207 h1 _29208). Qed.
Lemma lem2388665 (_29207 : int) (_29208 : int) : (term136 _29207 _29208) = (term127 _29207 _29208).
Proof. exact (eq_refl (term136 _29207 _29208)). Qed.
Lemma lem2388666 (_29207 : int) (_29208 : int) (h1 : term35) : term127 _29207 _29208.
Proof. exact (EQ_MP (@lem2388665 _29207 _29208) (@lem2388664 _29207 _29208 h1)). Qed.
Lemma lem2388673 (_29211 : int) (h1 : term35) : term135 _29211.
Proof. exact (@lem2388638 h1 _29211). Qed.
Lemma lem2388674 (_29211 : int) : (term135 _29211) = (term129 _29211).
Proof. exact (eq_refl (term135 _29211)). Qed.
Lemma lem2388675 (_29211 : int) (h1 : term35) : term129 _29211.
Proof. exact (EQ_MP (@lem2388674 _29211) (@lem2388673 _29211 h1)). Qed.
Lemma lem2388676 (_29211 : int) (_29212 : int) (h1 : term35) : term136 _29211 _29212.
Proof. exact (@lem2388675 _29211 h1 _29212). Qed.
Lemma lem2388677 (_29211 : int) (_29212 : int) : (term136 _29211 _29212) = (term127 _29211 _29212).
Proof. exact (eq_refl (term136 _29211 _29212)). Qed.
Lemma lem2388678 (_29211 : int) (_29212 : int) (h1 : term35) : term127 _29211 _29212.
Proof. exact (EQ_MP (@lem2388677 _29211 _29212) (@lem2388676 _29211 _29212 h1)). Qed.
Lemma lem2388679 (_29203 : int) (_29204 : int) (h1 : term35) : term125 _29203 _29204.
Proof. exact (proj2 (@lem2388654 _29203 _29204 h1)). Qed.
Lemma lem2388691 (_29211 : int) (_29212 : int) (h1 : term35) : term125 _29211 _29212.
Proof. exact (proj2 (@lem2388678 _29211 _29212 h1)). Qed.
Lemma lem2388700 (m : int) (n : int) (h1 : term132 m n) : term132 m n.
Proof. exact (h1). Qed.
Lemma lem2388718 (_29203 : int) (_29204 : int) (h1 : term35) : term137 _29203 _29204.
Proof. exact (proj2 (@lem2388679 _29203 _29204 h1)). Qed.
Lemma lem2388734 (m : int) (n : int) (h1 : term133 m n) : term133 m n.
Proof. exact (h1). Qed.
Lemma lem2388740 (_29207 : int) (_29208 : int) (h1 : term35) : term138 _29207 _29208.
Proof. exact (proj1 (@lem2388666 _29207 _29208 h1)). Qed.
Lemma lem2388768 (m : int) (n : int) (h1 : term134 m n) : term134 m n.
Proof. exact (h1). Qed.
Lemma lem2388780 (_29211 : int) (_29212 : int) (h1 : term35) : term139 _29211 _29212.
Proof. exact (proj1 (@lem2388691 _29211 _29212 h1)). Qed.
Lemma lem2388926 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (proj1 (@lem2388424 m n h1)). Qed.
Lemma lem2388927 (m : int) (n : int) (h1 : term54 m n) : term140 n.
Proof. exact (fun h0 : n = term13 => @lem2388926 m n h1). Qed.
Lemma lem2388929 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2388930 (n : int) : (term140 n) = (term56 n).
Proof. exact (@lem2388929 (n = term13)). Qed.
Lemma lem2388931 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (EQ_MP (@lem2388930 n) (@lem2388927 m n h1)). Qed.
Lemma lem2388937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2388938 (_29203 : int) (_29204 : int) : (term137 _29203 _29204) = (term142 _29203 _29204).
Proof. exact (@lem2388937 (_29203 = (term50 _29203 _29204)) (_29204 = term13)). Qed.
Lemma lem2388948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2388949 (_29203 : int) (_29204 : int) : (term143 _29203 _29204) = (term144 _29203 _29204).
Proof. exact (MK_COMB (@lem2388948) (@lem2388938 _29203 _29204)). Qed.
Lemma lem2388959 (_29203 : int) (_29204 : int) : (term142 _29203 _29204) = (term142 _29203 _29204).
Proof. exact (eq_refl (term142 _29203 _29204)). Qed.
Lemma lem2388960 (_29203 : int) (_29204 : int) : ((term137 _29203 _29204) = (term142 _29203 _29204)) = ((term142 _29203 _29204) = (term142 _29203 _29204)).
Proof. exact (MK_COMB (@lem2388949 _29203 _29204) (@lem2388959 _29203 _29204)). Qed.
Lemma lem2388962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2388963 (x : Prop) : (x = x) = True.
Proof. exact (@lem2388962 Prop x). Qed.
Lemma lem2388964 (_29203 : int) (_29204 : int) : ((term142 _29203 _29204) = (term142 _29203 _29204)) = True.
Proof. exact (@lem2388963 (term142 _29203 _29204)). Qed.
Lemma lem2388965 (_29203 : int) (_29204 : int) : ((term137 _29203 _29204) = (term142 _29203 _29204)) = True.
Proof. exact (TRANS (@lem2388960 _29203 _29204) (@lem2388964 _29203 _29204)). Qed.
Lemma lem2388966 (_29203 : int) (_29204 : int) : True = ((term137 _29203 _29204) = (term142 _29203 _29204)).
Proof. exact (SYM (@lem2388965 _29203 _29204)). Qed.
Lemma lem2388967 (_29203 : int) (_29204 : int) : (term137 _29203 _29204) = (term142 _29203 _29204).
Proof. exact (EQ_MP (@lem2388966 _29203 _29204) (@lem0)). Qed.
Lemma lem2388968 (_29203 : int) (_29204 : int) (h1 : term35) : term142 _29203 _29204.
Proof. exact (EQ_MP (@lem2388967 _29203 _29204) (@lem2388718 _29203 _29204 h1)). Qed.
Lemma lem2388970 (b : Prop) (a : Prop) : (a \/ b) = (term145 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2388973 (_29203 : int) (_29204 : int) : (term142 _29203 _29204) = (term146 _29203 _29204).
Proof. exact (@lem2388970 (_29204 = term13) (_29203 = (term50 _29203 _29204))). Qed.
Lemma lem2388976 (_29203 : int) (_29204 : int) (h1 : term35) : term146 _29203 _29204.
Proof. exact (EQ_MP (@lem2388973 _29203 _29204) (@lem2388968 _29203 _29204 h1)). Qed.
Lemma lem2388977 (_29203 : int) (n : int) (h1 : term35) : term146 _29203 n.
Proof. exact (@lem2388976 _29203 n h1). Qed.
Lemma lem2388980 (_29203 : int) (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : _29203 = (term50 _29203 n).
Proof. exact (@lem2388977 _29203 n h1 (@lem2388931 m n h2)). Qed.
Lemma lem2388981 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : m = (term50 m n).
Proof. exact (@lem2388980 m m n h1 h2). Qed.
Lemma lem2388982 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term147 m n.
Proof. exact (fun h0 : term132 m n => @lem2388981 m n h1 h2). Qed.
Lemma lem2388984 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2388985 (m : int) (n : int) : (term147 m n) = (m = (term50 m n)).
Proof. exact (@lem2388984 (m = (term50 m n))). Qed.
Lemma lem2388986 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : m = (term50 m n).
Proof. exact (EQ_MP (@lem2388985 m n) (@lem2388982 m n h1 h2)). Qed.
Lemma lem2388989 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2388991 (m : int) (n : int) : (term132 m n) = (term149 m n).
Proof. exact (@lem2388989 (m = (term50 m n))). Qed.
Lemma lem2388994 (m : int) (n : int) (h1 : term132 m n) : term149 m n.
Proof. exact (EQ_MP (@lem2388991 m n) (@lem2388700 m n h1)). Qed.
Lemma lem2388997 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : False.
Proof. exact (@lem2388994 m n h2 (@lem2388986 m n h1 h3)). Qed.
Lemma lem2388998 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : term150.
Proof. exact (fun h0 : ~ False => @lem2388997 m n h1 h2 h3). Qed.
Lemma lem2389000 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2389001 : term150 = False.
Proof. exact (@lem2389000 False). Qed.
Lemma lem2389002 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389001) (@lem2388998 m n h1 h2 h3)). Qed.
Lemma lem2389130 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (proj1 (@lem2388424 m n h1)). Qed.
Lemma lem2389131 (m : int) (n : int) (h1 : term54 m n) : term140 n.
Proof. exact (fun h0 : n = term13 => @lem2389130 m n h1). Qed.
Lemma lem2389133 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2389134 (n : int) : (term140 n) = (term56 n).
Proof. exact (@lem2389133 (n = term13)). Qed.
Lemma lem2389135 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (EQ_MP (@lem2389134 n) (@lem2389131 m n h1)). Qed.
Lemma lem2389148 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2389149 (_29207 : int) (_29208 : int) : (term151 _29207 _29208) = (term138 _29207 _29208).
Proof. exact (@lem2389148 (_29208 = term13) (term44 _29207 _29208)). Qed.
Lemma lem2389157 (_29207 : int) (_29208 : int) : (term152 _29207 _29208) = (term152 _29207 _29208).
Proof. exact (eq_refl (term152 _29207 _29208)). Qed.
Lemma lem2389158 (_29207 : int) (_29208 : int) : ((term138 _29207 _29208) = (term151 _29207 _29208)) = ((term138 _29207 _29208) = (term138 _29207 _29208)).
Proof. exact (MK_COMB (@lem2389157 _29207 _29208) (@lem2389149 _29207 _29208)). Qed.
Lemma lem2389160 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2389161 (x : Prop) : (x = x) = True.
Proof. exact (@lem2389160 Prop x). Qed.
Lemma lem2389162 (_29207 : int) (_29208 : int) : ((term138 _29207 _29208) = (term138 _29207 _29208)) = True.
Proof. exact (@lem2389161 (term138 _29207 _29208)). Qed.
Lemma lem2389163 (_29207 : int) (_29208 : int) : ((term138 _29207 _29208) = (term151 _29207 _29208)) = True.
Proof. exact (TRANS (@lem2389158 _29207 _29208) (@lem2389162 _29207 _29208)). Qed.
Lemma lem2389164 (_29207 : int) (_29208 : int) : True = ((term138 _29207 _29208) = (term151 _29207 _29208)).
Proof. exact (SYM (@lem2389163 _29207 _29208)). Qed.
Lemma lem2389165 (_29207 : int) (_29208 : int) : (term138 _29207 _29208) = (term151 _29207 _29208).
Proof. exact (EQ_MP (@lem2389164 _29207 _29208) (@lem0)). Qed.
Lemma lem2389166 (_29207 : int) (_29208 : int) (h1 : term35) : term151 _29207 _29208.
Proof. exact (EQ_MP (@lem2389165 _29207 _29208) (@lem2388740 _29207 _29208 h1)). Qed.
Lemma lem2389168 (b : Prop) (a : Prop) : (a \/ b) = (term145 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2389171 (_29207 : int) (_29208 : int) : (term151 _29207 _29208) = (term153 _29207 _29208).
Proof. exact (@lem2389168 (_29208 = term13) (term44 _29207 _29208)). Qed.
Lemma lem2389174 (_29207 : int) (_29208 : int) (h1 : term35) : term153 _29207 _29208.
Proof. exact (EQ_MP (@lem2389171 _29207 _29208) (@lem2389166 _29207 _29208 h1)). Qed.
Lemma lem2389175 (_29207 : int) (n : int) (h1 : term35) : term153 _29207 n.
Proof. exact (@lem2389174 _29207 n h1). Qed.
Lemma lem2389178 (_29207 : int) (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term44 _29207 n.
Proof. exact (@lem2389175 _29207 n h1 (@lem2389135 m n h2)). Qed.
Lemma lem2389179 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term44 m n.
Proof. exact (@lem2389178 m m n h1 h2). Qed.
Lemma lem2389180 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term154 m n.
Proof. exact (fun h0 : term133 m n => @lem2389179 m n h1 h2). Qed.
Lemma lem2389182 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2389183 (m : int) (n : int) : (term154 m n) = (term44 m n).
Proof. exact (@lem2389182 (term44 m n)). Qed.
Lemma lem2389184 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term44 m n.
Proof. exact (EQ_MP (@lem2389183 m n) (@lem2389180 m n h1 h2)). Qed.
Lemma lem2389187 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2389189 (m : int) (n : int) : (term133 m n) = (term155 m n).
Proof. exact (@lem2389187 (term44 m n)). Qed.
Lemma lem2389192 (m : int) (n : int) (h1 : term133 m n) : term155 m n.
Proof. exact (EQ_MP (@lem2389189 m n) (@lem2388734 m n h1)). Qed.
Lemma lem2389195 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : False.
Proof. exact (@lem2389192 m n h2 (@lem2389184 m n h1 h3)). Qed.
Lemma lem2389196 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : term150.
Proof. exact (fun h0 : ~ False => @lem2389195 m n h1 h2 h3). Qed.
Lemma lem2389198 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2389199 : term150 = False.
Proof. exact (@lem2389198 False). Qed.
Lemma lem2389200 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389199) (@lem2389196 m n h1 h2 h3)). Qed.
Lemma lem2389328 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (proj1 (@lem2388424 m n h1)). Qed.
Lemma lem2389329 (m : int) (n : int) (h1 : term54 m n) : term140 n.
Proof. exact (fun h0 : n = term13 => @lem2389328 m n h1). Qed.
Lemma lem2389331 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2389332 (n : int) : (term140 n) = (term56 n).
Proof. exact (@lem2389331 (n = term13)). Qed.
Lemma lem2389333 (m : int) (n : int) (h1 : term54 m n) : term56 n.
Proof. exact (EQ_MP (@lem2389332 n) (@lem2389329 m n h1)). Qed.
Lemma lem2389346 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2389347 (_29211 : int) (_29212 : int) : (term156 _29211 _29212) = (term139 _29211 _29212).
Proof. exact (@lem2389346 (_29212 = term13) (term45 _29211 _29212)). Qed.
Lemma lem2389355 (_29211 : int) (_29212 : int) : (term157 _29211 _29212) = (term157 _29211 _29212).
Proof. exact (eq_refl (term157 _29211 _29212)). Qed.
Lemma lem2389356 (_29211 : int) (_29212 : int) : ((term139 _29211 _29212) = (term156 _29211 _29212)) = ((term139 _29211 _29212) = (term139 _29211 _29212)).
Proof. exact (MK_COMB (@lem2389355 _29211 _29212) (@lem2389347 _29211 _29212)). Qed.
Lemma lem2389358 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2389359 (x : Prop) : (x = x) = True.
Proof. exact (@lem2389358 Prop x). Qed.
Lemma lem2389360 (_29211 : int) (_29212 : int) : ((term139 _29211 _29212) = (term139 _29211 _29212)) = True.
Proof. exact (@lem2389359 (term139 _29211 _29212)). Qed.
Lemma lem2389361 (_29211 : int) (_29212 : int) : ((term139 _29211 _29212) = (term156 _29211 _29212)) = True.
Proof. exact (TRANS (@lem2389356 _29211 _29212) (@lem2389360 _29211 _29212)). Qed.
Lemma lem2389362 (_29211 : int) (_29212 : int) : True = ((term139 _29211 _29212) = (term156 _29211 _29212)).
Proof. exact (SYM (@lem2389361 _29211 _29212)). Qed.
Lemma lem2389363 (_29211 : int) (_29212 : int) : (term139 _29211 _29212) = (term156 _29211 _29212).
Proof. exact (EQ_MP (@lem2389362 _29211 _29212) (@lem0)). Qed.
Lemma lem2389364 (_29211 : int) (_29212 : int) (h1 : term35) : term156 _29211 _29212.
Proof. exact (EQ_MP (@lem2389363 _29211 _29212) (@lem2388780 _29211 _29212 h1)). Qed.
Lemma lem2389366 (b : Prop) (a : Prop) : (a \/ b) = (term145 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2389369 (_29211 : int) (_29212 : int) : (term156 _29211 _29212) = (term158 _29211 _29212).
Proof. exact (@lem2389366 (_29212 = term13) (term45 _29211 _29212)). Qed.
Lemma lem2389372 (_29211 : int) (_29212 : int) (h1 : term35) : term158 _29211 _29212.
Proof. exact (EQ_MP (@lem2389369 _29211 _29212) (@lem2389364 _29211 _29212 h1)). Qed.
Lemma lem2389373 (_29211 : int) (n : int) (h1 : term35) : term158 _29211 n.
Proof. exact (@lem2389372 _29211 n h1). Qed.
Lemma lem2389376 (_29211 : int) (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term45 _29211 n.
Proof. exact (@lem2389373 _29211 n h1 (@lem2389333 m n h2)). Qed.
Lemma lem2389377 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term45 m n.
Proof. exact (@lem2389376 m m n h1 h2). Qed.
Lemma lem2389378 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term159 m n.
Proof. exact (fun h0 : term134 m n => @lem2389377 m n h1 h2). Qed.
Lemma lem2389380 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2389381 (m : int) (n : int) : (term159 m n) = (term45 m n).
Proof. exact (@lem2389380 (term45 m n)). Qed.
Lemma lem2389382 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : term45 m n.
Proof. exact (EQ_MP (@lem2389381 m n) (@lem2389378 m n h1 h2)). Qed.
Lemma lem2389385 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2389387 (m : int) (n : int) : (term134 m n) = (term160 m n).
Proof. exact (@lem2389385 (term45 m n)). Qed.
Lemma lem2389390 (m : int) (n : int) (h1 : term134 m n) : term160 m n.
Proof. exact (EQ_MP (@lem2389387 m n) (@lem2388768 m n h1)). Qed.
Lemma lem2389393 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : False.
Proof. exact (@lem2389390 m n h2 (@lem2389382 m n h1 h3)). Qed.
Lemma lem2389394 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : term150.
Proof. exact (fun h0 : ~ False => @lem2389393 m n h1 h2 h3). Qed.
Lemma lem2389396 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2389397 : term150 = False.
Proof. exact (@lem2389396 False). Qed.
Lemma lem2389398 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389397) (@lem2389394 m n h1 h2 h3)). Qed.
Lemma lem2389399 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : (term134 m n) = False.
Proof. exact (prop_ext (fun h4 : term134 m n => @lem2389398 m n h1 h2 h3) (fun h4 : False => @lem2388768 m n h2)). Qed.
Lemma lem2389400 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389399 m n h1 h2 h3) (@lem2388768 m n h2)). Qed.
Lemma lem2389401 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : (term133 m n) = False.
Proof. exact (prop_ext (fun h4 : term133 m n => @lem2389200 m n h1 h2 h3) (fun h4 : False => @lem2388734 m n h2)). Qed.
Lemma lem2389402 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389401 m n h1 h2 h3) (@lem2388734 m n h2)). Qed.
Lemma lem2389403 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : (term132 m n) = False.
Proof. exact (prop_ext (fun h4 : term132 m n => @lem2389002 m n h1 h2 h3) (fun h4 : False => @lem2388700 m n h2)). Qed.
Lemma lem2389404 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389403 m n h1 h2 h3) (@lem2388700 m n h2)). Qed.
Lemma lem2389405 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : (term134 m n) = False.
Proof. exact (prop_ext (fun h4 : term134 m n => @lem2389400 m n h1 h2 h3) (fun h4 : False => @lem2388642 m n h2)). Qed.
Lemma lem2389406 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389405 m n h1 h2 h3) (@lem2388642 m n h2)). Qed.
Lemma lem2389407 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : (term133 m n) = False.
Proof. exact (prop_ext (fun h4 : term133 m n => @lem2389402 m n h1 h2 h3) (fun h4 : False => @lem2388572 m n h2)). Qed.
Lemma lem2389408 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389407 m n h1 h2 h3) (@lem2388572 m n h2)). Qed.
Lemma lem2389409 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : (term132 m n) = False.
Proof. exact (prop_ext (fun h4 : term132 m n => @lem2389404 m n h1 h2 h3) (fun h4 : False => @lem2388502 m n h2)). Qed.
Lemma lem2389410 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389409 m n h1 h2 h3) (@lem2388502 m n h2)). Qed.
Lemma lem2389411 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : (term134 m n) = False.
Proof. exact (prop_ext (fun h4 : term134 m n => @lem2389406 m n h1 h2 h3) (fun h4 : False => @lem2388642 m n h2)). Qed.
Lemma lem2389412 (m : int) (n : int) (h1 : term35) (h2 : term134 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389411 m n h1 h2 h3) (@lem2388642 m n h2)). Qed.
Lemma lem2389413 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : (term133 m n) = False.
Proof. exact (prop_ext (fun h4 : term133 m n => @lem2389408 m n h1 h2 h3) (fun h4 : False => @lem2388572 m n h2)). Qed.
Lemma lem2389414 (m : int) (n : int) (h1 : term35) (h2 : term133 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389413 m n h1 h2 h3) (@lem2388572 m n h2)). Qed.
Lemma lem2389415 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : (term132 m n) = False.
Proof. exact (prop_ext (fun h4 : term132 m n => @lem2389410 m n h1 h2 h3) (fun h4 : False => @lem2388502 m n h2)). Qed.
Lemma lem2389416 (m : int) (n : int) (h1 : term35) (h2 : term132 m n) (h3 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389415 m n h1 h2 h3) (@lem2388502 m n h2)). Qed.
Lemma lem2389417 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) (h3 : term43 m n) : False.
Proof. exact (or_elim (@lem2388430 m n h3) (fun h0 : term133 m n => @lem2389414 m n h1 h0 h2) (fun h0 : term134 m n => @lem2389412 m n h1 h0 h2)). Qed.
Lemma lem2389418 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : False.
Proof. exact (or_elim (@lem2388425 m n h2) (fun h0 : term132 m n => @lem2389416 m n h1 h0 h2) (fun h0 : term43 m n => @lem2389417 m n h1 h2 h0)). Qed.
Lemma lem2389419 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : (term54 m n) = False.
Proof. exact (prop_ext (fun h3 : term54 m n => @lem2389418 m n h1 h2) (fun h3 : False => @lem2388424 m n h2)). Qed.
Lemma lem2389420 (m : int) (n : int) (h1 : term35) (h2 : term54 m n) : False.
Proof. exact (EQ_MP (@lem2389419 m n h1 h2) (@lem2388424 m n h2)). Qed.
Lemma lem2389421 (m : int) (h1 : term35) (h2 : term66 m) : False.
Proof. exact (ex_elim (@lem2388233 m h2) (fun n : int => fun h0 : term65 m n => @lem2389420 m n h1 h0)). Qed.
Lemma lem2389422 (h1 : term35) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2387935 h2) (fun m : int => fun h0 : term71 m => @lem2389421 m h1 h0)). Qed.
Lemma lem2389423 (h1 : term3) : term161.
Proof. exact (fun h0 : term35 => @lem2389422 h0 h1). Qed.
Lemma lem2389424 : term161 = term36.
Proof. exact (@lem69 term35). Qed.
Lemma lem2389425 (h1 : term3) : term36.
Proof. exact (EQ_MP (@lem2389424) (@lem2389423 h1)). Qed.
Lemma lem2389426 : term41.
Proof. exact (fun h0 : term3 => @lem2389425 h0). Qed.
Lemma lem2389427 : term4.
Proof. exact (EQ_MP (@lem2387837) (@lem2389426)). Qed.
Lemma lem2389429 : term4.
Proof. exact (@lem2387607 (@lem2389427)). Qed.
Lemma lem2389430 (h1 : term3) : term8.
Proof. exact (@lem2389429 (@lem2387592 h1)). Qed.
Lemma lem2389431 (h1 : term3) : False.
Proof. exact (@lem2389430 h1 (@lem2387577)). Qed.
Lemma lem2389432 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2389431 h1) (fun h2 : False => @lem2387592 h1)). Qed.
Lemma lem2389433 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2389432 h1) (@lem2387592 h1)). Qed.
Lemma lem2389434 : term2.
Proof. exact (fun h0 : term3 => @lem2389433 h0). Qed.
Lemma lem2389435 : term1.
Proof. exact (EQ_MP (@lem2387591) (@lem2389434)). Qed.
