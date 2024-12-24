Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_NONEMPTY_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3630650 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3630651 {_93152 : Type'} : (term1 _93152) = (term2 _93152).
Proof. exact (@lem3630650 (term1 _93152)). Qed.
Lemma lem3630652 {_93152 : Type'} : (term2 _93152) = (term1 _93152).
Proof. exact (SYM (@lem3630651 _93152)). Qed.
Lemma lem3630653 {_93152 : Type'} (h1 : term3 _93152) : term3 _93152.
Proof. exact (h1). Qed.
Lemma lem3630654 {_93152 : Type'} : term4 _93152.
Proof. exact (@lem3198543 _93152). Qed.
Lemma lem3630655 {_93152 : Type'} : term5 _93152.
Proof. exact (@lem3197565 _93152). Qed.
Lemma lem3630659 {_93152 : Type'} (h1 : term6 _93152) : term6 _93152.
Proof. exact (h1). Qed.
Lemma lem3630660 {_93152 : Type'} : term7 _93152.
Proof. exact (fun h0 : term6 _93152 => @lem3630659 _93152 h0). Qed.
Lemma lem3630661 {_93152 : Type'} (h1 : term7 _93152) : term7 _93152.
Proof. exact (h1). Qed.
Lemma lem3630662 {_93152 : Type'} (h1 : term6 _93152) : term6 _93152.
Proof. exact (h1). Qed.
Lemma lem3630663 {_93152 : Type'} (h1 : term6 _93152) (h2 : term7 _93152) : term6 _93152.
Proof. exact (@lem3630661 _93152 h2 (@lem3630662 _93152 h1)). Qed.
Lemma lem3630664 {_93152 : Type'} (h1 : term6 _93152) : term8 _93152.
Proof. exact (fun h0 : term7 _93152 => @lem3630663 _93152 h1 h0). Qed.
Lemma lem3630665 {_93152 : Type'} (h1 : term7 _93152) : term7 _93152.
Proof. exact (h1). Qed.
Lemma lem3630666 {_93152 : Type'} (h1 : term6 _93152) (h2 : term7 _93152) : term6 _93152.
Proof. exact (@lem3630664 _93152 h1 (@lem3630665 _93152 h2)). Qed.
Lemma lem3630667 {_93152 : Type'} (h1 : term7 _93152) : term7 _93152.
Proof. exact (fun h0 : term6 _93152 => @lem3630666 _93152 h0 h1). Qed.
Lemma lem3630668 {_93152 : Type'} : term9 _93152.
Proof. exact (fun h0 : term7 _93152 => @lem3630667 _93152 h0). Qed.
Lemma lem3630671 {_93152 : Type'} : term7 _93152.
Proof. exact (@lem3630668 _93152 (@lem3630660 _93152)). Qed.
Lemma lem3630672 {_93152 : Type'} : term7 _93152.
Proof. exact (@lem3630671 _93152). Qed.
Lemma lem3630696 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3630697 {_93152 : Type'} : (term10 _93152) = (term11 _93152).
Proof. exact (@lem3630696 (term4 _93152)). Qed.
Lemma lem3630702 {_93152 : Type'} : (term12 _93152) = (term12 _93152).
Proof. exact (eq_refl (term12 _93152)). Qed.
Lemma lem3630703 {_93152 : Type'} : (term13 _93152) = (term14 _93152).
Proof. exact (MK_COMB (@lem3630702 _93152) (@lem3630697 _93152)). Qed.
Lemma lem3630706 {_93152 : Type'} : (term15 _93152) = (term15 _93152).
Proof. exact (eq_refl (term15 _93152)). Qed.
Lemma lem3630713 {_93152 : Type'} : (term6 _93152) = (term16 _93152).
Proof. exact (MK_COMB (@lem3630706 _93152) (@lem3630703 _93152)). Qed.
Lemma lem3630720 {_93152 : Type'} (s : _93152 -> Prop) : ((@INFINITE _93152 s) = (term17 _93152 s)) = ((@INFINITE _93152 s) = (term17 _93152 s)).
Proof. exact (eq_refl ((@INFINITE _93152 s) = (term17 _93152 s))). Qed.
Lemma lem3630721 {_93152 : Type'} : (term18 _93152) = (term18 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630720 _93152 s)). Qed.
Lemma lem3630722 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630723 {_93152 : Type'} : (term4 _93152) = (term4 _93152).
Proof. exact (MK_COMB (@lem3630722 _93152) (@lem3630721 _93152)). Qed.
Lemma lem3630724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3630725 {_93152 : Type'} : (term11 _93152) = (term11 _93152).
Proof. exact (MK_COMB (@lem3630724) (@lem3630723 _93152)). Qed.
Lemma lem3630730 {_93152 : Type'} (x : _93152) (s : _93152 -> Prop) : (term19 _93152 x s) = (term19 _93152 x s).
Proof. exact (eq_refl (term19 _93152 x s)). Qed.
Lemma lem3630731 {_93152 : Type'} (x : _93152) : (term20 _93152 x) = (term20 _93152 x).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630730 _93152 x s)). Qed.
Lemma lem3630732 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630733 {_93152 : Type'} (x : _93152) : (term21 _93152 x) = (term21 _93152 x).
Proof. exact (MK_COMB (@lem3630732 _93152) (@lem3630731 _93152 x)). Qed.
Lemma lem3630734 {_93152 : Type'} : (term22 _93152) = (term22 _93152).
Proof. exact (fun_ext (fun x : _93152 => @lem3630733 _93152 x)). Qed.
Lemma lem3630735 {_93152 : Type'} : (@all _93152) = (@all _93152).
Proof. exact (eq_refl (@all _93152)). Qed.
Lemma lem3630736 {_93152 : Type'} : (term23 _93152) = (term23 _93152).
Proof. exact (MK_COMB (@lem3630735 _93152) (@lem3630734 _93152)). Qed.
Lemma lem3630739 {_93152 : Type'} : (term24 _93152) = (term24 _93152).
Proof. exact (eq_refl (term24 _93152)). Qed.
Lemma lem3630740 {_93152 : Type'} : (term5 _93152) = (term5 _93152).
Proof. exact (MK_COMB (@lem3630739 _93152) (@lem3630736 _93152)). Qed.
Lemma lem3630741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3630742 {_93152 : Type'} : (term12 _93152) = (term12 _93152).
Proof. exact (MK_COMB (@lem3630741) (@lem3630740 _93152)). Qed.
Lemma lem3630743 {_93152 : Type'} : (term14 _93152) = (term14 _93152).
Proof. exact (MK_COMB (@lem3630742 _93152) (@lem3630725 _93152)). Qed.
Lemma lem3630750 {_93152 : Type'} (s : _93152 -> Prop) : (term25 _93152 s) = (term25 _93152 s).
Proof. exact (eq_refl (term25 _93152 s)). Qed.
Lemma lem3630751 {_93152 : Type'} : (term26 _93152) = (term26 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630750 _93152 s)). Qed.
Lemma lem3630752 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630753 {_93152 : Type'} : (term1 _93152) = (term1 _93152).
Proof. exact (MK_COMB (@lem3630752 _93152) (@lem3630751 _93152)). Qed.
Lemma lem3630754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3630755 {_93152 : Type'} : (term3 _93152) = (term3 _93152).
Proof. exact (MK_COMB (@lem3630754) (@lem3630753 _93152)). Qed.
Lemma lem3630756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3630757 {_93152 : Type'} : (term15 _93152) = (term15 _93152).
Proof. exact (MK_COMB (@lem3630756) (@lem3630755 _93152)). Qed.
Lemma lem3630758 {_93152 : Type'} : (term16 _93152) = (term16 _93152).
Proof. exact (MK_COMB (@lem3630757 _93152) (@lem3630743 _93152)). Qed.
Lemma lem3630795 {_93152 : Type'} : (term6 _93152) = (term16 _93152).
Proof. exact (TRANS (@lem3630713 _93152) (@lem3630758 _93152)). Qed.
Lemma lem3630796 {_93152 : Type'} : (term16 _93152) = (term6 _93152).
Proof. exact (SYM (@lem3630795 _93152)). Qed.
Lemma lem3630797 {_93152 : Type'} (h1 : term3 _93152) : term3 _93152.
Proof. exact (h1). Qed.
Lemma lem3630798 {_93152 : Type'} (h1 : term5 _93152) : term5 _93152.
Proof. exact (h1). Qed.
Lemma lem3630799 {_93152 : Type'} (h1 : term4 _93152) : term4 _93152.
Proof. exact (h1). Qed.
Lemma lem3630803 {_93152 : Type'} (s : _93152 -> Prop) : (term27 _93152 s) = (s = (@EMPTY _93152)).
Proof. exact (@lem16933 (s = (@EMPTY _93152))). Qed.
Lemma lem3630805 {_93152 : Type'} (s : _93152 -> Prop) : (term28 _93152 s) = (term28 _93152 s).
Proof. exact (eq_refl (term28 _93152 s)). Qed.
Lemma lem3630806 {_93152 : Type'} (s : _93152 -> Prop) : (term29 _93152 s) = (term30 _93152 s).
Proof. exact (MK_COMB (@lem3630805 _93152 s) (@lem3630803 _93152 s)). Qed.
Lemma lem3630807 {_93152 : Type'} (s : _93152 -> Prop) : (term31 _93152 s) = (term29 _93152 s).
Proof. exact (@lem17362 (@INFINITE _93152 s) (term32 _93152 s)). Qed.
Lemma lem3630808 {_93152 : Type'} (s : _93152 -> Prop) : (term31 _93152 s) = (term30 _93152 s).
Proof. exact (TRANS (@lem3630807 _93152 s) (@lem3630806 _93152 s)). Qed.
Lemma lem3630809 {_93152 : Type'} (P : type686 _93152) : (term33 _93152 P) = (term34 _93152 P).
Proof. exact (@lem18392 (_93152 -> Prop) P). Qed.
Lemma lem3630810 {_93152 : Type'} : (term3 _93152) = (term35 _93152).
Proof. exact (@lem3630809 _93152 (term26 _93152)). Qed.
Lemma lem3630811 {_93152 : Type'} (s : _93152 -> Prop) : (term36 _93152 s) = (term25 _93152 s).
Proof. exact (eq_refl (term36 _93152 s)). Qed.
Lemma lem3630812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3630813 {_93152 : Type'} (s : _93152 -> Prop) : (term37 _93152 s) = (term31 _93152 s).
Proof. exact (MK_COMB (@lem3630812) (@lem3630811 _93152 s)). Qed.
Lemma lem3630814 {_93152 : Type'} (s : _93152 -> Prop) : (term37 _93152 s) = (term30 _93152 s).
Proof. exact (TRANS (@lem3630813 _93152 s) (@lem3630808 _93152 s)). Qed.
Lemma lem3630815 {_93152 : Type'} : (term38 _93152) = (term39 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630814 _93152 s)). Qed.
Lemma lem3630816 {_93152 : Type'} : (@ex (_93152 -> Prop)) = (@ex (_93152 -> Prop)).
Proof. exact (eq_refl (@ex (_93152 -> Prop))). Qed.
Lemma lem3630817 {_93152 : Type'} : (term35 _93152) = (term40 _93152).
Proof. exact (MK_COMB (@lem3630816 _93152) (@lem3630815 _93152)). Qed.
Lemma lem3630850 {_93152 : Type'} : (term3 _93152) = (term40 _93152).
Proof. exact (TRANS (@lem3630810 _93152) (@lem3630817 _93152)). Qed.
Lemma lem3630851 {_93152 : Type'} (h1 : term3 _93152) : term40 _93152.
Proof. exact (EQ_MP (@lem3630850 _93152) (@lem3630797 _93152 h1)). Qed.
Lemma lem3630859 {_93152 : Type'} (x : _93152) (s : _93152 -> Prop) : (term19 _93152 x s) = (term41 _93152 x s).
Proof. exact (@lem17265 (@FINITE _93152 s) (term42 _93152 x s)). Qed.
Lemma lem3630860 {_93152 : Type'} (x : _93152) : (term20 _93152 x) = (term43 _93152 x).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630859 _93152 x s)). Qed.
Lemma lem3630861 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630862 {_93152 : Type'} (x : _93152) : (term21 _93152 x) = (term44 _93152 x).
Proof. exact (MK_COMB (@lem3630861 _93152) (@lem3630860 _93152 x)). Qed.
Lemma lem3630863 {_93152 : Type'} : (term22 _93152) = (term45 _93152).
Proof. exact (fun_ext (fun x : _93152 => @lem3630862 _93152 x)). Qed.
Lemma lem3630864 {_93152 : Type'} : (@all _93152) = (@all _93152).
Proof. exact (eq_refl (@all _93152)). Qed.
Lemma lem3630865 {_93152 : Type'} : (term23 _93152) = (term46 _93152).
Proof. exact (MK_COMB (@lem3630864 _93152) (@lem3630863 _93152)). Qed.
Lemma lem3630867 {_93152 : Type'} : (term24 _93152) = (term24 _93152).
Proof. exact (eq_refl (term24 _93152)). Qed.
Lemma lem3630924 {_93152 : Type'} : (term5 _93152) = (term47 _93152).
Proof. exact (MK_COMB (@lem3630867 _93152) (@lem3630865 _93152)). Qed.
Lemma lem3630925 {_93152 : Type'} (h1 : term5 _93152) : term47 _93152.
Proof. exact (EQ_MP (@lem3630924 _93152) (@lem3630798 _93152 h1)). Qed.
Lemma lem3630931 {_93152 : Type'} (s : _93152 -> Prop) : (term48 _93152 s) = (@FINITE _93152 s).
Proof. exact (@lem16933 (@FINITE _93152 s)). Qed.
Lemma lem3630934 {_93152 : Type'} (s : _93152 -> Prop) : (term49 _93152 s) = (term49 _93152 s).
Proof. exact (eq_refl (term49 _93152 s)). Qed.
Lemma lem3630936 {_93152 : Type'} (s : _93152 -> Prop) : (term50 _93152 s) = (term50 _93152 s).
Proof. exact (eq_refl (term50 _93152 s)). Qed.
Lemma lem3630937 {_93152 : Type'} (s : _93152 -> Prop) : (term51 _93152 s) = (term52 _93152 s).
Proof. exact (MK_COMB (@lem3630936 _93152 s) (@lem3630931 _93152 s)). Qed.
Lemma lem3630938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3630939 {_93152 : Type'} (s : _93152 -> Prop) : (term53 _93152 s) = (term54 _93152 s).
Proof. exact (MK_COMB (@lem3630938) (@lem3630937 _93152 s)). Qed.
Lemma lem3630940 {_93152 : Type'} (s : _93152 -> Prop) : (term55 _93152 s) = (term56 _93152 s).
Proof. exact (MK_COMB (@lem3630939 _93152 s) (@lem3630934 _93152 s)). Qed.
Lemma lem3630941 {_93152 : Type'} (s : _93152 -> Prop) : ((@INFINITE _93152 s) = (term17 _93152 s)) = (term55 _93152 s).
Proof. exact (@lem17784 (@INFINITE _93152 s) (term17 _93152 s)). Qed.
Lemma lem3630942 {_93152 : Type'} (s : _93152 -> Prop) : ((@INFINITE _93152 s) = (term17 _93152 s)) = (term56 _93152 s).
Proof. exact (TRANS (@lem3630941 _93152 s) (@lem3630940 _93152 s)). Qed.
Lemma lem3630943 {_93152 : Type'} : (term18 _93152) = (term57 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630942 _93152 s)). Qed.
Lemma lem3630944 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630945 {_93152 : Type'} : (term4 _93152) = (term58 _93152).
Proof. exact (MK_COMB (@lem3630944 _93152) (@lem3630943 _93152)). Qed.
Lemma lem3630947 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3630948 {_93152 : Type'} (P : type686 _93152) (Q : type686 _93152) : (term61 _93152 P Q) = (term62 _93152 P Q).
Proof. exact (@lem3630947 (_93152 -> Prop) P Q). Qed.
Lemma lem3630949 {_93152 : Type'} : (term63 _93152) = (term64 _93152).
Proof. exact (@lem3630948 _93152 (term65 _93152) (term66 _93152)). Qed.
Lemma lem3630950 {_93152 : Type'} (s : _93152 -> Prop) : (term67 _93152 s) = (term52 _93152 s).
Proof. exact (eq_refl (term67 _93152 s)). Qed.
Lemma lem3630951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3630952 {_93152 : Type'} (s : _93152 -> Prop) : (term68 _93152 s) = (term54 _93152 s).
Proof. exact (MK_COMB (@lem3630951) (@lem3630950 _93152 s)). Qed.
Lemma lem3630953 {_93152 : Type'} (s : _93152 -> Prop) : (term69 _93152 s) = (term49 _93152 s).
Proof. exact (eq_refl (term69 _93152 s)). Qed.
Lemma lem3630954 {_93152 : Type'} (s : _93152 -> Prop) : (term70 _93152 s) = (term56 _93152 s).
Proof. exact (MK_COMB (@lem3630952 _93152 s) (@lem3630953 _93152 s)). Qed.
Lemma lem3630955 {_93152 : Type'} : (term71 _93152) = (term57 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630954 _93152 s)). Qed.
Lemma lem3630956 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630957 {_93152 : Type'} : (term63 _93152) = (term58 _93152).
Proof. exact (MK_COMB (@lem3630956 _93152) (@lem3630955 _93152)). Qed.
Lemma lem3630958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3630959 {_93152 : Type'} : (term72 _93152) = (term73 _93152).
Proof. exact (MK_COMB (@lem3630958) (@lem3630957 _93152)). Qed.
Lemma lem3630960 {_93152 : Type'} (s : _93152 -> Prop) : (term67 _93152 s) = (term52 _93152 s).
Proof. exact (eq_refl (term67 _93152 s)). Qed.
Lemma lem3630961 {_93152 : Type'} : (term74 _93152) = (term65 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630960 _93152 s)). Qed.
Lemma lem3630962 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630963 {_93152 : Type'} : (term75 _93152) = (term76 _93152).
Proof. exact (MK_COMB (@lem3630962 _93152) (@lem3630961 _93152)). Qed.
Lemma lem3630964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3630965 {_93152 : Type'} : (term77 _93152) = (term78 _93152).
Proof. exact (MK_COMB (@lem3630964) (@lem3630963 _93152)). Qed.
Lemma lem3630966 {_93152 : Type'} (s : _93152 -> Prop) : (term69 _93152 s) = (term49 _93152 s).
Proof. exact (eq_refl (term69 _93152 s)). Qed.
Lemma lem3630967 {_93152 : Type'} : (term79 _93152) = (term66 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3630966 _93152 s)). Qed.
Lemma lem3630968 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3630969 {_93152 : Type'} : (term80 _93152) = (term81 _93152).
Proof. exact (MK_COMB (@lem3630968 _93152) (@lem3630967 _93152)). Qed.
Lemma lem3630970 {_93152 : Type'} : (term64 _93152) = (term82 _93152).
Proof. exact (MK_COMB (@lem3630965 _93152) (@lem3630969 _93152)). Qed.
Lemma lem3630971 {_93152 : Type'} : ((term63 _93152) = (term64 _93152)) = ((term58 _93152) = (term82 _93152)).
Proof. exact (MK_COMB (@lem3630959 _93152) (@lem3630970 _93152)). Qed.
Lemma lem3631034 {_93152 : Type'} : (term58 _93152) = (term82 _93152).
Proof. exact (EQ_MP (@lem3630971 _93152) (@lem3630949 _93152)). Qed.
Lemma lem3631035 {_93152 : Type'} : (term4 _93152) = (term82 _93152).
Proof. exact (TRANS (@lem3630945 _93152) (@lem3631034 _93152)). Qed.
Lemma lem3631036 {_93152 : Type'} (h1 : term4 _93152) : term82 _93152.
Proof. exact (EQ_MP (@lem3631035 _93152) (@lem3630799 _93152 h1)). Qed.
Lemma lem3631052 {_93152 : Type'} (x : _93152) (s : _93152 -> Prop) : (term41 _93152 x s) = (term41 _93152 x s).
Proof. exact (eq_refl (term41 _93152 x s)). Qed.
Lemma lem3631053 {_93152 : Type'} (x : _93152) : (term43 _93152 x) = (term43 _93152 x).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3631052 _93152 x s)). Qed.
Lemma lem3631054 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3631055 {_93152 : Type'} (x : _93152) : (term44 _93152 x) = (term44 _93152 x).
Proof. exact (MK_COMB (@lem3631054 _93152) (@lem3631053 _93152 x)). Qed.
Lemma lem3631056 {_93152 : Type'} : (term45 _93152) = (term45 _93152).
Proof. exact (fun_ext (fun x : _93152 => @lem3631055 _93152 x)). Qed.
Lemma lem3631057 {_93152 : Type'} : (@all _93152) = (@all _93152).
Proof. exact (eq_refl (@all _93152)). Qed.
Lemma lem3631058 {_93152 : Type'} : (term46 _93152) = (term46 _93152).
Proof. exact (MK_COMB (@lem3631057 _93152) (@lem3631056 _93152)). Qed.
Lemma lem3631063 {_93152 : Type'} : (term24 _93152) = (term24 _93152).
Proof. exact (eq_refl (term24 _93152)). Qed.
Lemma lem3631064 {_93152 : Type'} : (term47 _93152) = (term47 _93152).
Proof. exact (MK_COMB (@lem3631063 _93152) (@lem3631058 _93152)). Qed.
Lemma lem3631065 {_93152 : Type'} (h1 : term5 _93152) : term47 _93152.
Proof. exact (EQ_MP (@lem3631064 _93152) (@lem3630925 _93152 h1)). Qed.
Lemma lem3631078 {_93152 : Type'} (s : _93152 -> Prop) : (term49 _93152 s) = (term49 _93152 s).
Proof. exact (eq_refl (term49 _93152 s)). Qed.
Lemma lem3631079 {_93152 : Type'} : (term66 _93152) = (term66 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3631078 _93152 s)). Qed.
Lemma lem3631080 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3631081 {_93152 : Type'} : (term81 _93152) = (term81 _93152).
Proof. exact (MK_COMB (@lem3631080 _93152) (@lem3631079 _93152)). Qed.
Lemma lem3631090 {_93152 : Type'} (s : _93152 -> Prop) : (term52 _93152 s) = (term52 _93152 s).
Proof. exact (eq_refl (term52 _93152 s)). Qed.
Lemma lem3631091 {_93152 : Type'} : (term65 _93152) = (term65 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3631090 _93152 s)). Qed.
Lemma lem3631092 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3631093 {_93152 : Type'} : (term76 _93152) = (term76 _93152).
Proof. exact (MK_COMB (@lem3631092 _93152) (@lem3631091 _93152)). Qed.
Lemma lem3631094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3631095 {_93152 : Type'} : (term78 _93152) = (term78 _93152).
Proof. exact (MK_COMB (@lem3631094) (@lem3631093 _93152)). Qed.
Lemma lem3631096 {_93152 : Type'} : (term82 _93152) = (term82 _93152).
Proof. exact (MK_COMB (@lem3631095 _93152) (@lem3631081 _93152)). Qed.
Lemma lem3631097 {_93152 : Type'} (h1 : term4 _93152) : term82 _93152.
Proof. exact (EQ_MP (@lem3631096 _93152) (@lem3631036 _93152 h1)). Qed.
Lemma lem3631109 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : term30 _93152 s.
Proof. exact (h1). Qed.
Lemma lem3631112 {_93152 : Type'} (h1 : term4 _93152) : term81 _93152.
Proof. exact (proj2 (@lem3631097 _93152 h1)). Qed.
Lemma lem3631144 {_93152 : Type'} (s : _93152 -> Prop) : (term49 _93152 s) = (term49 _93152 s).
Proof. exact (eq_refl (term49 _93152 s)). Qed.
Lemma lem3631145 {_93152 : Type'} : (term66 _93152) = (term66 _93152).
Proof. exact (fun_ext (fun s : _93152 -> Prop => @lem3631144 _93152 s)). Qed.
Lemma lem3631146 {_93152 : Type'} : (@all (_93152 -> Prop)) = (@all (_93152 -> Prop)).
Proof. exact (eq_refl (@all (_93152 -> Prop))). Qed.
Lemma lem3631148 {_93152 : Type'} : (term81 _93152) = (term81 _93152).
Proof. exact (MK_COMB (@lem3631146 _93152) (@lem3631145 _93152)). Qed.
Lemma lem3631149 {_93152 : Type'} (h1 : term4 _93152) : term81 _93152.
Proof. exact (EQ_MP (@lem3631148 _93152) (@lem3631112 _93152 h1)). Qed.
Lemma lem3631173 {_93152 : Type'} (_39611 : _93152 -> Prop) (h1 : term4 _93152) : term69 _93152 _39611.
Proof. exact (@lem3631149 _93152 h1 _39611). Qed.
Lemma lem3631174 {_93152 : Type'} (_39611 : _93152 -> Prop) : (term69 _93152 _39611) = (term49 _93152 _39611).
Proof. exact (eq_refl (term69 _93152 _39611)). Qed.
Lemma lem3631183 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : @INFINITE _93152 s.
Proof. exact (proj1 (@lem3631109 _93152 s h1)). Qed.
Lemma lem3631185 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : s = (@EMPTY _93152).
Proof. exact (proj2 (@lem3631109 _93152 s h1)). Qed.
Lemma lem3631220 {_93152 : Type'} : (term83 _93152) = (term83 _93152).
Proof. exact (eq_refl (term83 _93152)). Qed.
Lemma lem3631221 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : (term84 _93152 s) = (term85 _93152).
Proof. exact (MK_COMB (@lem3631220 _93152) (@lem3631185 _93152 s h1)). Qed.
Lemma lem3631222 {_93152 : Type'} : (term85 _93152) = (@INFINITE _93152 (@EMPTY _93152)).
Proof. exact (eq_refl (term85 _93152)). Qed.
Lemma lem3631223 {_93152 : Type'} (s : _93152 -> Prop) : (term86 _93152 s) = (term86 _93152 s).
Proof. exact (eq_refl (term86 _93152 s)). Qed.
Lemma lem3631224 {_93152 : Type'} (s : _93152 -> Prop) : ((term84 _93152 s) = (term85 _93152)) = ((term84 _93152 s) = (@INFINITE _93152 (@EMPTY _93152))).
Proof. exact (MK_COMB (@lem3631223 _93152 s) (@lem3631222 _93152)). Qed.
Lemma lem3631225 {_93152 : Type'} (s : _93152 -> Prop) : (term84 _93152 s) = (@INFINITE _93152 s).
Proof. exact (eq_refl (term84 _93152 s)). Qed.
Lemma lem3631226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3631227 {_93152 : Type'} (s : _93152 -> Prop) : (term86 _93152 s) = (term87 _93152 s).
Proof. exact (MK_COMB (@lem3631226) (@lem3631225 _93152 s)). Qed.
Lemma lem3631228 {_93152 : Type'} : (@INFINITE _93152 (@EMPTY _93152)) = (@INFINITE _93152 (@EMPTY _93152)).
Proof. exact (eq_refl (@INFINITE _93152 (@EMPTY _93152))). Qed.
Lemma lem3631229 {_93152 : Type'} (s : _93152 -> Prop) : ((term84 _93152 s) = (@INFINITE _93152 (@EMPTY _93152))) = ((@INFINITE _93152 s) = (@INFINITE _93152 (@EMPTY _93152))).
Proof. exact (MK_COMB (@lem3631227 _93152 s) (@lem3631228 _93152)). Qed.
Lemma lem3631230 {_93152 : Type'} (s : _93152 -> Prop) : ((term84 _93152 s) = (term85 _93152)) = ((@INFINITE _93152 s) = (@INFINITE _93152 (@EMPTY _93152))).
Proof. exact (TRANS (@lem3631224 _93152 s) (@lem3631229 _93152 s)). Qed.
Lemma lem3631231 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : (@INFINITE _93152 s) = (@INFINITE _93152 (@EMPTY _93152)).
Proof. exact (EQ_MP (@lem3631230 _93152 s) (@lem3631221 _93152 s h1)). Qed.
Lemma lem3631260 {_93152 : Type'} (_39611 : _93152 -> Prop) (h1 : term4 _93152) : term49 _93152 _39611.
Proof. exact (EQ_MP (@lem3631174 _93152 _39611) (@lem3631173 _93152 _39611 h1)). Qed.
Lemma lem3631290 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : @INFINITE _93152 (@EMPTY _93152).
Proof. exact (EQ_MP (@lem3631231 _93152 s h1) (@lem3631183 _93152 s h1)). Qed.
Lemma lem3631291 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : term88 _93152.
Proof. exact (fun h0 : term89 _93152 => @lem3631290 _93152 s h1). Qed.
Lemma lem3631293 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3631294 {_93152 : Type'} : (term88 _93152) = (@INFINITE _93152 (@EMPTY _93152)).
Proof. exact (@lem3631293 (@INFINITE _93152 (@EMPTY _93152))). Qed.
Lemma lem3631295 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term30 _93152 s) : @INFINITE _93152 (@EMPTY _93152).
Proof. exact (EQ_MP (@lem3631294 _93152) (@lem3631291 _93152 s h1)). Qed.
Lemma lem3631297 {_93152 : Type'} (h1 : term5 _93152) : @FINITE _93152 (@EMPTY _93152).
Proof. exact (proj1 (@lem3631065 _93152 h1)). Qed.
Lemma lem3631298 {_93152 : Type'} (h1 : term5 _93152) : term91 _93152.
Proof. exact (fun h0 : term92 _93152 => @lem3631297 _93152 h1). Qed.
Lemma lem3631300 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3631301 {_93152 : Type'} : (term91 _93152) = (@FINITE _93152 (@EMPTY _93152)).
Proof. exact (@lem3631300 (@FINITE _93152 (@EMPTY _93152))). Qed.
Lemma lem3631302 {_93152 : Type'} (h1 : term5 _93152) : @FINITE _93152 (@EMPTY _93152).
Proof. exact (EQ_MP (@lem3631301 _93152) (@lem3631298 _93152 h1)). Qed.
Lemma lem3631304 (a : Prop) (b : Prop) : (term93 a b) = (term94 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3631305 {_93152 : Type'} (_39611 : _93152 -> Prop) : (term49 _93152 _39611) = (term95 _93152 _39611).
Proof. exact (@lem3631304 (@INFINITE _93152 _39611) (@FINITE _93152 _39611)). Qed.
Lemma lem3631307 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3631308 {_93152 : Type'} (_39611 : _93152 -> Prop) : (term95 _93152 _39611) = (term96 _93152 _39611).
Proof. exact (@lem3631307 (term97 _93152 _39611)). Qed.
Lemma lem3631309 {_93152 : Type'} (_39611 : _93152 -> Prop) : (term49 _93152 _39611) = (term96 _93152 _39611).
Proof. exact (TRANS (@lem3631305 _93152 _39611) (@lem3631308 _93152 _39611)). Qed.
Lemma lem3631311 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term5 _93152) (h2 : term30 _93152 s) : term98 _93152.
Proof. exact (conj (@lem3631295 _93152 s h2) (@lem3631302 _93152 h1)). Qed.
Lemma lem3631313 {_93152 : Type'} (_39611 : _93152 -> Prop) (h1 : term4 _93152) : term96 _93152 _39611.
Proof. exact (EQ_MP (@lem3631309 _93152 _39611) (@lem3631260 _93152 _39611 h1)). Qed.
Lemma lem3631314 {_93152 : Type'} (_39611 : _93152 -> Prop) (h1 : term4 _93152) : term96 _93152 _39611.
Proof. exact (@lem3631313 _93152 _39611 h1). Qed.
Lemma lem3631315 {_93152 : Type'} (h1 : term4 _93152) : term99 _93152.
Proof. exact (@lem3631314 _93152 (@EMPTY _93152) h1). Qed.
Lemma lem3631318 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term4 _93152) (h2 : term5 _93152) (h3 : term30 _93152 s) : False.
Proof. exact (@lem3631315 _93152 h1 (@lem3631311 _93152 s h2 h3)). Qed.
Lemma lem3631319 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term4 _93152) (h2 : term5 _93152) (h3 : term30 _93152 s) : term100.
Proof. exact (fun h0 : ~ False => @lem3631318 _93152 s h1 h2 h3). Qed.
Lemma lem3631321 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3631322 : term100 = False.
Proof. exact (@lem3631321 False). Qed.
Lemma lem3631324 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term4 _93152) (h2 : term5 _93152) (h3 : term30 _93152 s) : False.
Proof. exact (EQ_MP (@lem3631322) (@lem3631319 _93152 s h1 h2 h3)). Qed.
Lemma lem3631325 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term4 _93152) (h2 : term5 _93152) (h3 : term30 _93152 s) : (term30 _93152 s) = False.
Proof. exact (prop_ext (fun h4 : term30 _93152 s => @lem3631324 _93152 s h1 h2 h3) (fun h4 : False => @lem3631109 _93152 s h3)). Qed.
Lemma lem3631326 {_93152 : Type'} (s : _93152 -> Prop) (h1 : term4 _93152) (h2 : term5 _93152) (h3 : term30 _93152 s) : False.
Proof. exact (EQ_MP (@lem3631325 _93152 s h1 h2 h3) (@lem3631109 _93152 s h3)). Qed.
Lemma lem3631327 {_93152 : Type'} (h1 : term4 _93152) (h2 : term3 _93152) (h3 : term5 _93152) : False.
Proof. exact (ex_elim (@lem3630851 _93152 h2) (fun s : _93152 -> Prop => fun h0 : term39 _93152 s => @lem3631326 _93152 s h1 h3 h0)). Qed.
Lemma lem3631328 {_93152 : Type'} (h1 : term3 _93152) (h2 : term5 _93152) : term10 _93152.
Proof. exact (fun h0 : term4 _93152 => @lem3631327 _93152 h0 h1 h2). Qed.
Lemma lem3631329 {_93152 : Type'} : (term10 _93152) = (term11 _93152).
Proof. exact (@lem69 (term4 _93152)). Qed.
Lemma lem3631330 {_93152 : Type'} (h1 : term3 _93152) (h2 : term5 _93152) : term11 _93152.
Proof. exact (EQ_MP (@lem3631329 _93152) (@lem3631328 _93152 h1 h2)). Qed.
Lemma lem3631331 {_93152 : Type'} (h1 : term3 _93152) : term14 _93152.
Proof. exact (fun h0 : term5 _93152 => @lem3631330 _93152 h1 h0). Qed.
Lemma lem3631332 {_93152 : Type'} : term16 _93152.
Proof. exact (fun h0 : term3 _93152 => @lem3631331 _93152 h0). Qed.
Lemma lem3631333 {_93152 : Type'} : term6 _93152.
Proof. exact (EQ_MP (@lem3630796 _93152) (@lem3631332 _93152)). Qed.
Lemma lem3631335 {_93152 : Type'} : term6 _93152.
Proof. exact (@lem3630672 _93152 (@lem3631333 _93152)). Qed.
Lemma lem3631336 {_93152 : Type'} (h1 : term3 _93152) : term13 _93152.
Proof. exact (@lem3631335 _93152 (@lem3630653 _93152 h1)). Qed.
Lemma lem3631337 {_93152 : Type'} (h1 : term3 _93152) : term10 _93152.
Proof. exact (@lem3631336 _93152 h1 (@lem3630655 _93152)). Qed.
Lemma lem3631338 {_93152 : Type'} (h1 : term3 _93152) : False.
Proof. exact (@lem3631337 _93152 h1 (@lem3630654 _93152)). Qed.
Lemma lem3631339 {_93152 : Type'} (h1 : term3 _93152) : (term3 _93152) = False.
Proof. exact (prop_ext (fun h2 : term3 _93152 => @lem3631338 _93152 h1) (fun h2 : False => @lem3630653 _93152 h1)). Qed.
Lemma lem3631340 {_93152 : Type'} (h1 : term3 _93152) : False.
Proof. exact (EQ_MP (@lem3631339 _93152 h1) (@lem3630653 _93152 h1)). Qed.
Lemma lem3631341 {_93152 : Type'} : term2 _93152.
Proof. exact (fun h0 : term3 _93152 => @lem3631340 _93152 h0). Qed.
Lemma lem3631342 {_93152 : Type'} : term1 _93152.
Proof. exact (EQ_MP (@lem3630652 _93152) (@lem3631341 _93152)). Qed.
