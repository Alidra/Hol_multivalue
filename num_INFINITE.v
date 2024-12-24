Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_INFINITE_term_abbrevs.
Require Import INFINITE_spec.
Require Import IN_UNIV_spec.
Require Import num_FINITE_AVOID_spec.
Require Import thm0_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4628789 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4628790 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@INFINITE A s) = (term1 A s)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4628793 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term1 A s).
Proof. exact (EQ_MP (@lem4628790 A s) (@lem4628789 A s)). Qed.
Lemma lem4628794 (s : nat -> Prop) : (@INFINITE nat s) = (term2 s).
Proof. exact (@lem4628793 nat s). Qed.
Lemma lem4628795 : (@INFINITE nat (@UNIV nat)) = term3.
Proof. exact (@lem4628794 (@UNIV nat)). Qed.
Lemma lem4628796 : term3 = (@INFINITE nat (@UNIV nat)).
Proof. exact (SYM (@lem4628795)). Qed.
Lemma lem4628797 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4628798 : term4.
Proof. exact (@lem3204818 nat). Qed.
Lemma lem4628802 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4628803 : term6.
Proof. exact (fun h0 : term5 => @lem4628802 h0). Qed.
Lemma lem4628804 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem4628805 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4628806 (h1 : term5) (h2 : term6) : term5.
Proof. exact (@lem4628804 h2 (@lem4628805 h1)). Qed.
Lemma lem4628807 (h1 : term5) : term7.
Proof. exact (fun h0 : term6 => @lem4628806 h1 h0). Qed.
Lemma lem4628808 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem4628809 (h1 : term5) (h2 : term6) : term5.
Proof. exact (@lem4628807 h1 (@lem4628808 h2)). Qed.
Lemma lem4628810 (h1 : term6) : term6.
Proof. exact (fun h0 : term5 => @lem4628809 h0 h1). Qed.
Lemma lem4628811 : term8.
Proof. exact (fun h0 : term6 => @lem4628810 h0). Qed.
Lemma lem4628814 : term6.
Proof. exact (@lem4628811 (@lem4628803)). Qed.
Lemma lem4628824 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4628825 : term9 = term10.
Proof. exact (@lem4628824 term11). Qed.
Lemma lem4628836 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem4628837 : term13 = term14.
Proof. exact (MK_COMB (@lem4628836) (@lem4628825)). Qed.
Lemma lem4628840 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem4628847 : term5 = term16.
Proof. exact (MK_COMB (@lem4628840) (@lem4628837)). Qed.
Lemma lem4628850 (a : nat) (s : nat -> Prop) : (term17 a s) = (term17 a s).
Proof. exact (eq_refl (term17 a s)). Qed.
Lemma lem4628851 (s : nat -> Prop) : (term18 s) = (term18 s).
Proof. exact (fun_ext (fun a : nat => @lem4628850 a s)). Qed.
Lemma lem4628852 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4628853 (s : nat -> Prop) : (term19 s) = (term19 s).
Proof. exact (MK_COMB (@lem4628852) (@lem4628851 s)). Qed.
Lemma lem4628856 (s : nat -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem4628857 (s : nat -> Prop) : (term21 s) = (term21 s).
Proof. exact (MK_COMB (@lem4628856 s) (@lem4628853 s)). Qed.
Lemma lem4628858 : term22 = term22.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4628857 s)). Qed.
Lemma lem4628859 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4628860 : term11 = term11.
Proof. exact (MK_COMB (@lem4628859) (@lem4628858)). Qed.
Lemma lem4628861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4628862 : term10 = term10.
Proof. exact (MK_COMB (@lem4628861) (@lem4628860)). Qed.
Lemma lem4628863 (x : nat) : (@IN nat x (@UNIV nat)) = (@IN nat x (@UNIV nat)).
Proof. exact (eq_refl (@IN nat x (@UNIV nat))). Qed.
Lemma lem4628864 : term23 = term23.
Proof. exact (fun_ext (fun x : nat => @lem4628863 x)). Qed.
Lemma lem4628865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628866 : term4 = term4.
Proof. exact (MK_COMB (@lem4628865) (@lem4628864)). Qed.
Lemma lem4628867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4628868 : term12 = term12.
Proof. exact (MK_COMB (@lem4628867) (@lem4628866)). Qed.
Lemma lem4628869 : term14 = term14.
Proof. exact (MK_COMB (@lem4628868) (@lem4628862)). Qed.
Lemma lem4628872 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem4628873 : term16 = term16.
Proof. exact (MK_COMB (@lem4628872) (@lem4628869)). Qed.
Lemma lem4628900 : term5 = term16.
Proof. exact (TRANS (@lem4628847) (@lem4628873)). Qed.
Lemma lem4628901 : term16 = term5.
Proof. exact (SYM (@lem4628900)). Qed.
Lemma lem4628903 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4628904 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem4628910 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4628911 (x : nat) : (@IN nat x (@UNIV nat)) = (@IN nat x (@UNIV nat)).
Proof. exact (eq_refl (@IN nat x (@UNIV nat))). Qed.
Lemma lem4628912 : term23 = term23.
Proof. exact (fun_ext (fun x : nat => @lem4628911 x)). Qed.
Lemma lem4628913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4628922 : term4 = term4.
Proof. exact (MK_COMB (@lem4628913) (@lem4628912)). Qed.
Lemma lem4628923 (h1 : term4) : term4.
Proof. exact (EQ_MP (@lem4628922) (@lem4628903 h1)). Qed.
Lemma lem4628925 (a : nat) (s : nat -> Prop) : (term17 a s) = (term17 a s).
Proof. exact (eq_refl (term17 a s)). Qed.
Lemma lem4628926 (s : nat -> Prop) : (term18 s) = (term18 s).
Proof. exact (fun_ext (fun a : nat => @lem4628925 a s)). Qed.
Lemma lem4628927 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4628928 (s : nat -> Prop) : (term19 s) = (term19 s).
Proof. exact (MK_COMB (@lem4628927) (@lem4628926 s)). Qed.
Lemma lem4628930 (s : nat -> Prop) : (term24 s) = (term24 s).
Proof. exact (eq_refl (term24 s)). Qed.
Lemma lem4628931 (s : nat -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem4628930 s) (@lem4628928 s)). Qed.
Lemma lem4628932 (s : nat -> Prop) : (term21 s) = (term25 s).
Proof. exact (@lem17265 (@FINITE nat s) (term19 s)). Qed.
Lemma lem4628933 (s : nat -> Prop) : (term21 s) = (term25 s).
Proof. exact (TRANS (@lem4628932 s) (@lem4628931 s)). Qed.
Lemma lem4628934 : term22 = term26.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4628933 s)). Qed.
Lemma lem4628935 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4628936 : term11 = term27.
Proof. exact (MK_COMB (@lem4628935) (@lem4628934)). Qed.
Lemma lem4628991 {A : Type'} (P : Prop) (Q : A -> Prop) : (term28 A P Q) = (term29 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4628992 (P : Prop) (Q : nat -> Prop) : (term30 P Q) = (term31 P Q).
Proof. exact (@lem4628991 nat P Q). Qed.
Lemma lem4628993 (s : nat -> Prop) : (term32 s) = (term33 s).
Proof. exact (@lem4628992 (term2 s) (term18 s)). Qed.
Lemma lem4628994 (a : nat) (s : nat -> Prop) : (term34 s a) = (term17 a s).
Proof. exact (eq_refl (term34 s a)). Qed.
Lemma lem4628995 (s : nat -> Prop) : (term35 s) = (term18 s).
Proof. exact (fun_ext (fun a : nat => @lem4628994 a s)). Qed.
Lemma lem4628996 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4628997 (s : nat -> Prop) : (term36 s) = (term19 s).
Proof. exact (MK_COMB (@lem4628996) (@lem4628995 s)). Qed.
Lemma lem4628998 (s : nat -> Prop) : (term24 s) = (term24 s).
Proof. exact (eq_refl (term24 s)). Qed.
Lemma lem4628999 (s : nat -> Prop) : (term32 s) = (term25 s).
Proof. exact (MK_COMB (@lem4628998 s) (@lem4628997 s)). Qed.
Lemma lem4629000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4629001 (s : nat -> Prop) : (term37 s) = (term38 s).
Proof. exact (MK_COMB (@lem4629000) (@lem4628999 s)). Qed.
Lemma lem4629002 (a : nat) (s : nat -> Prop) : (term34 s a) = (term17 a s).
Proof. exact (eq_refl (term34 s a)). Qed.
Lemma lem4629003 (s : nat -> Prop) : (term24 s) = (term24 s).
Proof. exact (eq_refl (term24 s)). Qed.
Lemma lem4629004 (a : nat) (s : nat -> Prop) : (term39 s a) = (term40 a s).
Proof. exact (MK_COMB (@lem4629003 s) (@lem4629002 a s)). Qed.
Lemma lem4629005 (s : nat -> Prop) : (term41 s) = (term42 s).
Proof. exact (fun_ext (fun a : nat => @lem4629004 a s)). Qed.
Lemma lem4629006 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4629007 (s : nat -> Prop) : (term33 s) = (term43 s).
Proof. exact (MK_COMB (@lem4629006) (@lem4629005 s)). Qed.
Lemma lem4629008 (s : nat -> Prop) : ((term32 s) = (term33 s)) = ((term25 s) = (term43 s)).
Proof. exact (MK_COMB (@lem4629001 s) (@lem4629007 s)). Qed.
Lemma lem4629009 (s : nat -> Prop) : (term25 s) = (term43 s).
Proof. exact (EQ_MP (@lem4629008 s) (@lem4628993 s)). Qed.
Lemma lem4629010 : term26 = term44.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4629009 s)). Qed.
Lemma lem4629011 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4629012 : term27 = term45.
Proof. exact (MK_COMB (@lem4629011) (@lem4629010)). Qed.
Lemma lem4629014 {A B : Type'} (P : type1413 A B) : (term46 A B P) = (term47 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4629015 (P : type991) : (term48 P) = (term49 P).
Proof. exact (@lem4629014 (nat -> Prop) nat P). Qed.
Lemma lem4629016 : term50 = term51.
Proof. exact (@lem4629015 term52). Qed.
Lemma lem4629017 (s : nat -> Prop) : (term53 s) = (term42 s).
Proof. exact (eq_refl (term53 s)). Qed.
Lemma lem4629018 (a : nat) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4629019 (s : nat -> Prop) (a : nat) : (term54 s a) = (term55 s a).
Proof. exact (MK_COMB (@lem4629017 s) (@lem4629018 a)). Qed.
Lemma lem4629020 (a : nat) (s : nat -> Prop) : (term55 s a) = (term40 a s).
Proof. exact (eq_refl (term55 s a)). Qed.
Lemma lem4629021 (a : nat) (s : nat -> Prop) : (term54 s a) = (term40 a s).
Proof. exact (TRANS (@lem4629019 s a) (@lem4629020 a s)). Qed.
Lemma lem4629022 (s : nat -> Prop) : (term56 s) = (term42 s).
Proof. exact (fun_ext (fun a : nat => @lem4629021 a s)). Qed.
Lemma lem4629023 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4629024 (s : nat -> Prop) : (term57 s) = (term43 s).
Proof. exact (MK_COMB (@lem4629023) (@lem4629022 s)). Qed.
Lemma lem4629025 : term58 = term44.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4629024 s)). Qed.
Lemma lem4629026 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4629027 : term50 = term45.
Proof. exact (MK_COMB (@lem4629026) (@lem4629025)). Qed.
Lemma lem4629028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4629029 : term59 = term60.
Proof. exact (MK_COMB (@lem4629028) (@lem4629027)). Qed.
Lemma lem4629030 (s : nat -> Prop) : (term53 s) = (term42 s).
Proof. exact (eq_refl (term53 s)). Qed.
Lemma lem4629031 (a : type994) (s : nat -> Prop) : (a s) = (a s).
Proof. exact (eq_refl (a s)). Qed.
Lemma lem4629032 (a : type994) (s : nat -> Prop) : (term61 a s) = (term62 a s).
Proof. exact (MK_COMB (@lem4629030 s) (@lem4629031 a s)). Qed.
Lemma lem4629033 (a : type994) (s : nat -> Prop) : (term62 a s) = (term63 a s).
Proof. exact (eq_refl (term62 a s)). Qed.
Lemma lem4629034 (a : type994) (s : nat -> Prop) : (term61 a s) = (term63 a s).
Proof. exact (TRANS (@lem4629032 a s) (@lem4629033 a s)). Qed.
Lemma lem4629035 (a : type994) : (term64 a) = (term65 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4629034 a s)). Qed.
Lemma lem4629036 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4629037 (a : type994) : (term66 a) = (term67 a).
Proof. exact (MK_COMB (@lem4629036) (@lem4629035 a)). Qed.
Lemma lem4629038 : term68 = term69.
Proof. exact (fun_ext (fun a : type994 => @lem4629037 a)). Qed.
Lemma lem4629039 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem4629040 : term51 = term70.
Proof. exact (MK_COMB (@lem4629039) (@lem4629038)). Qed.
Lemma lem4629041 : (term50 = term51) = (term45 = term70).
Proof. exact (MK_COMB (@lem4629029) (@lem4629040)). Qed.
Lemma lem4629042 : term45 = term70.
Proof. exact (EQ_MP (@lem4629041) (@lem4629016)). Qed.
Lemma lem4629044 : term27 = term70.
Proof. exact (TRANS (@lem4629012) (@lem4629042)). Qed.
Lemma lem4629045 : term11 = term70.
Proof. exact (TRANS (@lem4628936) (@lem4629044)). Qed.
Lemma lem4629046 (h1 : term11) : term70.
Proof. exact (EQ_MP (@lem4629045) (@lem4628904 h1)). Qed.
Lemma lem4629047 (a : type994) (h1 : term67 a) : term67 a.
Proof. exact (h1). Qed.
Lemma lem4629051 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4629056 (x : nat) : (@IN nat x (@UNIV nat)) = (@IN nat x (@UNIV nat)).
Proof. exact (eq_refl (@IN nat x (@UNIV nat))). Qed.
Lemma lem4629057 : term23 = term23.
Proof. exact (fun_ext (fun x : nat => @lem4629056 x)). Qed.
Lemma lem4629058 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629059 : term4 = term4.
Proof. exact (MK_COMB (@lem4629058) (@lem4629057)). Qed.
Lemma lem4629060 (h1 : term4) : term4.
Proof. exact (EQ_MP (@lem4629059) (@lem4628923 h1)). Qed.
Lemma lem4629077 (a : type994) (s : nat -> Prop) : (term63 a s) = (term63 a s).
Proof. exact (eq_refl (term63 a s)). Qed.
Lemma lem4629078 (a : type994) : (term65 a) = (term65 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4629077 a s)). Qed.
Lemma lem4629079 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4629080 (a : type994) : (term67 a) = (term67 a).
Proof. exact (MK_COMB (@lem4629079) (@lem4629078 a)). Qed.
Lemma lem4629081 (a : type994) (h1 : term67 a) : term67 a.
Proof. exact (EQ_MP (@lem4629080 a) (@lem4629047 a h1)). Qed.
Lemma lem4629085 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4629087 (x : nat) : (@IN nat x (@UNIV nat)) = (@IN nat x (@UNIV nat)).
Proof. exact (eq_refl (@IN nat x (@UNIV nat))). Qed.
Lemma lem4629088 : term23 = term23.
Proof. exact (fun_ext (fun x : nat => @lem4629087 x)). Qed.
Lemma lem4629089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629091 : term4 = term4.
Proof. exact (MK_COMB (@lem4629089) (@lem4629088)). Qed.
Lemma lem4629092 (h1 : term4) : term4.
Proof. exact (EQ_MP (@lem4629091) (@lem4629060 h1)). Qed.
Lemma lem4629100 (a : type994) (s : nat -> Prop) : (term63 a s) = (term63 a s).
Proof. exact (eq_refl (term63 a s)). Qed.
Lemma lem4629101 (a : type994) : (term65 a) = (term65 a).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4629100 a s)). Qed.
Lemma lem4629102 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4629104 (a : type994) : (term67 a) = (term67 a).
Proof. exact (MK_COMB (@lem4629102) (@lem4629101 a)). Qed.
Lemma lem4629105 (a : type994) (h1 : term67 a) : term67 a.
Proof. exact (EQ_MP (@lem4629104 a) (@lem4629081 a h1)). Qed.
Lemma lem4629106 (_55601 : nat) (h1 : term4) : term71 _55601.
Proof. exact (@lem4629092 h1 _55601). Qed.
Lemma lem4629107 (_55601 : nat) : (term71 _55601) = (@IN nat _55601 (@UNIV nat)).
Proof. exact (eq_refl (term71 _55601)). Qed.
Lemma lem4629109 (_55602 : nat -> Prop) (a : type994) (h1 : term67 a) : term72 a _55602.
Proof. exact (@lem4629105 a h1 _55602). Qed.
Lemma lem4629110 (a : type994) (_55602 : nat -> Prop) : (term72 a _55602) = (term63 a _55602).
Proof. exact (eq_refl (term72 a _55602)). Qed.
Lemma lem4629113 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4629121 (_55602 : nat -> Prop) (a : type994) (h1 : term67 a) : term63 a _55602.
Proof. exact (EQ_MP (@lem4629110 a _55602) (@lem4629109 _55602 a h1)). Qed.
Lemma lem4629123 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4629124 (h1 : @FINITE nat (@UNIV nat)) : term73.
Proof. exact (fun h0 : term3 => @lem4629123 h1). Qed.
Lemma lem4629126 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629127 : term73 = (@FINITE nat (@UNIV nat)).
Proof. exact (@lem4629126 (@FINITE nat (@UNIV nat))). Qed.
Lemma lem4629128 (h1 : @FINITE nat (@UNIV nat)) : @FINITE nat (@UNIV nat).
Proof. exact (EQ_MP (@lem4629127) (@lem4629124 h1)). Qed.
Lemma lem4629130 (_55601 : nat) (h1 : term4) : @IN nat _55601 (@UNIV nat).
Proof. exact (EQ_MP (@lem4629107 _55601) (@lem4629106 _55601 h1)). Qed.
Lemma lem4629131 (a : type994) (h1 : term4) : term75 a.
Proof. exact (@lem4629130 (a (@UNIV nat)) h1). Qed.
Lemma lem4629132 (a : type994) (h1 : term4) : term76 a.
Proof. exact (fun h0 : term77 a => @lem4629131 a h1). Qed.
Lemma lem4629134 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629135 (a : type994) : (term76 a) = (term75 a).
Proof. exact (@lem4629134 (term75 a)). Qed.
Lemma lem4629136 (a : type994) (h1 : term4) : term75 a.
Proof. exact (EQ_MP (@lem4629135 a) (@lem4629132 a h1)). Qed.
Lemma lem4629138 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4629139 (a : type994) (_55602 : nat -> Prop) : (term63 a _55602) = (term80 a _55602).
Proof. exact (@lem4629138 (@FINITE nat _55602) (term81 a _55602)). Qed.
Lemma lem4629141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4629142 (a : type994) (_55602 : nat -> Prop) : (term80 a _55602) = (term82 a _55602).
Proof. exact (@lem4629141 (term83 a _55602)). Qed.
Lemma lem4629143 (a : type994) (_55602 : nat -> Prop) : (term63 a _55602) = (term82 a _55602).
Proof. exact (TRANS (@lem4629139 a _55602) (@lem4629142 a _55602)). Qed.
Lemma lem4629145 (a : type994) (h1 : term4) (h2 : @FINITE nat (@UNIV nat)) : term84 a.
Proof. exact (conj (@lem4629128 h2) (@lem4629136 a h1)). Qed.
Lemma lem4629147 (_55602 : nat -> Prop) (a : type994) (h1 : term67 a) : term82 a _55602.
Proof. exact (EQ_MP (@lem4629143 a _55602) (@lem4629121 _55602 a h1)). Qed.
Lemma lem4629148 (a : type994) (h1 : term67 a) : term85 a.
Proof. exact (@lem4629147 (@UNIV nat) a h1). Qed.
Lemma lem4629151 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (@lem4629148 a h1 (@lem4629145 a h2 h3)). Qed.
Lemma lem4629152 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : term86.
Proof. exact (fun h0 : ~ False => @lem4629151 a h1 h2 h3). Qed.
Lemma lem4629154 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629155 : term86 = False.
Proof. exact (@lem4629154 False). Qed.
Lemma lem4629156 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629155) (@lem4629152 a h1 h2 h3)). Qed.
Lemma lem4629157 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE nat (@UNIV nat) => @lem4629156 a h1 h2 h3) (fun h4 : False => @lem4629113 h3)). Qed.
Lemma lem4629158 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629157 a h1 h2 h3) (@lem4629113 h3)). Qed.
Lemma lem4629159 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE nat (@UNIV nat) => @lem4629158 a h1 h2 h3) (fun h4 : False => @lem4629085 h3)). Qed.
Lemma lem4629160 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629159 a h1 h2 h3) (@lem4629085 h3)). Qed.
Lemma lem4629161 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (term67 a) = False.
Proof. exact (prop_ext (fun h4 : term67 a => @lem4629160 a h1 h2 h3) (fun h4 : False => @lem4629105 a h1)). Qed.
Lemma lem4629162 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629161 a h1 h2 h3) (@lem4629105 a h1)). Qed.
Lemma lem4629163 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : term4 = False.
Proof. exact (prop_ext (fun h4 : term4 => @lem4629162 a h1 h2 h3) (fun h4 : False => @lem4629092 h2)). Qed.
Lemma lem4629164 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629163 a h1 h2 h3) (@lem4629092 h2)). Qed.
Lemma lem4629165 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE nat (@UNIV nat) => @lem4629164 a h1 h2 h3) (fun h4 : False => @lem4629085 h3)). Qed.
Lemma lem4629166 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629165 a h1 h2 h3) (@lem4629085 h3)). Qed.
Lemma lem4629167 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (term67 a) = False.
Proof. exact (prop_ext (fun h4 : term67 a => @lem4629166 a h1 h2 h3) (fun h4 : False => @lem4629081 a h1)). Qed.
Lemma lem4629168 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629167 a h1 h2 h3) (@lem4629081 a h1)). Qed.
Lemma lem4629169 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : term4 = False.
Proof. exact (prop_ext (fun h4 : term4 => @lem4629168 a h1 h2 h3) (fun h4 : False => @lem4629060 h2)). Qed.
Lemma lem4629170 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629169 a h1 h2 h3) (@lem4629060 h2)). Qed.
Lemma lem4629171 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE nat (@UNIV nat) => @lem4629170 a h1 h2 h3) (fun h4 : False => @lem4629051 h3)). Qed.
Lemma lem4629172 (a : type994) (h1 : term67 a) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629171 a h1 h2 h3) (@lem4629051 h3)). Qed.
Lemma lem4629173 (h1 : term11) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (ex_elim (@lem4629046 h1) (fun a : type994 => fun h0 : term69 a => @lem4629172 a h0 h2 h3)). Qed.
Lemma lem4629174 (h1 : term11) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : term4 = False.
Proof. exact (prop_ext (fun h4 : term4 => @lem4629173 h1 h2 h3) (fun h4 : False => @lem4628923 h2)). Qed.
Lemma lem4629175 (h1 : term11) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629174 h1 h2 h3) (@lem4628923 h2)). Qed.
Lemma lem4629176 (h1 : term11) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h4 : @FINITE nat (@UNIV nat) => @lem4629175 h1 h2 h3) (fun h4 : False => @lem4628910 h3)). Qed.
Lemma lem4629177 (h1 : term11) (h2 : term4) (h3 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629176 h1 h2 h3) (@lem4628910 h3)). Qed.
Lemma lem4629178 (h1 : term4) (h2 : @FINITE nat (@UNIV nat)) : term9.
Proof. exact (fun h0 : term11 => @lem4629177 h0 h1 h2). Qed.
Lemma lem4629179 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem4629180 (h1 : term4) (h2 : @FINITE nat (@UNIV nat)) : term10.
Proof. exact (EQ_MP (@lem4629179) (@lem4629178 h1 h2)). Qed.
Lemma lem4629181 (h1 : @FINITE nat (@UNIV nat)) : term14.
Proof. exact (fun h0 : term4 => @lem4629180 h0 h1). Qed.
Lemma lem4629182 : term16.
Proof. exact (fun h0 : @FINITE nat (@UNIV nat) => @lem4629181 h0). Qed.
Lemma lem4629183 : term5.
Proof. exact (EQ_MP (@lem4628901) (@lem4629182)). Qed.
Lemma lem4629185 : term5.
Proof. exact (@lem4628814 (@lem4629183)). Qed.
Lemma lem4629186 (h1 : @FINITE nat (@UNIV nat)) : term13.
Proof. exact (@lem4629185 (@lem4628797 h1)). Qed.
Lemma lem4629187 (h1 : @FINITE nat (@UNIV nat)) : term9.
Proof. exact (@lem4629186 h1 (@lem4628798)). Qed.
Lemma lem4629188 (h1 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (@lem4629187 h1 (@lem4626359)). Qed.
Lemma lem4629189 (h1 : @FINITE nat (@UNIV nat)) : (@FINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h2 : @FINITE nat (@UNIV nat) => @lem4629188 h1) (fun h2 : False => @lem4628797 h1)). Qed.
Lemma lem4629190 (h1 : @FINITE nat (@UNIV nat)) : False.
Proof. exact (EQ_MP (@lem4629189 h1) (@lem4628797 h1)). Qed.
Lemma lem4629191 : term87.
Proof. exact (fun h0 : @FINITE nat (@UNIV nat) => @lem4629190 h0). Qed.
Lemma lem4629192 : term87 = term3.
Proof. exact (@lem69 (@FINITE nat (@UNIV nat))). Qed.
Lemma lem4629193 : term3.
Proof. exact (EQ_MP (@lem4629192) (@lem4629191)). Qed.
Lemma lem4629194 : @INFINITE nat (@UNIV nat).
Proof. exact (EQ_MP (@lem4628796) (@lem4629193)). Qed.
