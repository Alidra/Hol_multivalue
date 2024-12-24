Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTEGER_REAL_OF_INT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm2267738_spec.
Require Import thm69_spec.
Lemma lem2267802 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2267803 : term1 = term2.
Proof. exact (@lem2267802 term1). Qed.
Lemma lem2267804 : term2 = term1.
Proof. exact (SYM (@lem2267803)). Qed.
Lemma lem2267805 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2267808 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2267809 : term5.
Proof. exact (fun h0 : term4 => @lem2267808 h0). Qed.
Lemma lem2267810 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2267811 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2267812 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2267810 h2 (@lem2267811 h1)). Qed.
Lemma lem2267813 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2267812 h1 h0). Qed.
Lemma lem2267814 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2267815 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2267813 h1 (@lem2267814 h2)). Qed.
Lemma lem2267816 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2267815 h0 h1). Qed.
Lemma lem2267817 : term7.
Proof. exact (fun h0 : term5 => @lem2267816 h0). Qed.
Lemma lem2267820 : term5.
Proof. exact (@lem2267817 (@lem2267809)). Qed.
Lemma lem2267828 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2267829 : term8 = term9.
Proof. exact (@lem2267828 term10). Qed.
Lemma lem2267840 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2267847 : term4 = term12.
Proof. exact (MK_COMB (@lem2267840) (@lem2267829)). Qed.
Lemma lem2267852 (r : real) : ((integer r) = ((term13 r) = r)) = ((integer r) = ((term13 r) = r)).
Proof. exact (eq_refl ((integer r) = ((term13 r) = r))). Qed.
Lemma lem2267853 : term14 = term14.
Proof. exact (fun_ext (fun r : real => @lem2267852 r)). Qed.
Lemma lem2267854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2267855 : term15 = term15.
Proof. exact (MK_COMB (@lem2267854) (@lem2267853)). Qed.
Lemma lem2267856 (a : int) : ((term16 a) = a) = ((term16 a) = a).
Proof. exact (eq_refl ((term16 a) = a)). Qed.
Lemma lem2267857 : term17 = term17.
Proof. exact (fun_ext (fun a : int => @lem2267856 a)). Qed.
Lemma lem2267858 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2267859 : term18 = term18.
Proof. exact (MK_COMB (@lem2267858) (@lem2267857)). Qed.
Lemma lem2267860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2267861 : term19 = term19.
Proof. exact (MK_COMB (@lem2267860) (@lem2267859)). Qed.
Lemma lem2267862 : term10 = term10.
Proof. exact (MK_COMB (@lem2267861) (@lem2267855)). Qed.
Lemma lem2267863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2267864 : term9 = term9.
Proof. exact (MK_COMB (@lem2267863) (@lem2267862)). Qed.
Lemma lem2267865 (x : int) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2267866 : term21 = term21.
Proof. exact (fun_ext (fun x : int => @lem2267865 x)). Qed.
Lemma lem2267867 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2267868 : term1 = term1.
Proof. exact (MK_COMB (@lem2267867) (@lem2267866)). Qed.
Lemma lem2267869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2267870 : term3 = term3.
Proof. exact (MK_COMB (@lem2267869) (@lem2267868)). Qed.
Lemma lem2267871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2267872 : term11 = term11.
Proof. exact (MK_COMB (@lem2267871) (@lem2267870)). Qed.
Lemma lem2267873 : term12 = term12.
Proof. exact (MK_COMB (@lem2267872) (@lem2267864)). Qed.
Lemma lem2267898 : term4 = term12.
Proof. exact (TRANS (@lem2267847) (@lem2267873)). Qed.
Lemma lem2267899 : term12 = term4.
Proof. exact (SYM (@lem2267898)). Qed.
Lemma lem2267900 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2267901 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2267903 (P : int -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2267904 : term3 = term24.
Proof. exact (@lem2267903 term21). Qed.
Lemma lem2267905 (x : int) : (term25 x) = (term20 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2267906 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2267908 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2267906) (@lem2267905 x)). Qed.
Lemma lem2267909 : term28 = term29.
Proof. exact (fun_ext (fun x : int => @lem2267908 x)). Qed.
Lemma lem2267910 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2267911 : term24 = term30.
Proof. exact (MK_COMB (@lem2267910) (@lem2267909)). Qed.
Lemma lem2267920 : term3 = term30.
Proof. exact (TRANS (@lem2267904) (@lem2267911)). Qed.
Lemma lem2267921 (h1 : term3) : term30.
Proof. exact (EQ_MP (@lem2267920) (@lem2267900 h1)). Qed.
Lemma lem2267922 (a : int) : ((term16 a) = a) = ((term16 a) = a).
Proof. exact (eq_refl ((term16 a) = a)). Qed.
Lemma lem2267923 : term17 = term17.
Proof. exact (fun_ext (fun a : int => @lem2267922 a)). Qed.
Lemma lem2267924 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2267925 : term18 = term18.
Proof. exact (MK_COMB (@lem2267924) (@lem2267923)). Qed.
Lemma lem2267940 (r : real) : ((integer r) = ((term13 r) = r)) = (term31 r).
Proof. exact (@lem17784 (integer r) ((term13 r) = r)). Qed.
Lemma lem2267941 : term14 = term32.
Proof. exact (fun_ext (fun r : real => @lem2267940 r)). Qed.
Lemma lem2267942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2267943 : term15 = term33.
Proof. exact (MK_COMB (@lem2267942) (@lem2267941)). Qed.
Lemma lem2267944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2267945 : term19 = term19.
Proof. exact (MK_COMB (@lem2267944) (@lem2267925)). Qed.
Lemma lem2267946 : term10 = term34.
Proof. exact (MK_COMB (@lem2267945) (@lem2267943)). Qed.
Lemma lem2267952 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2267953 (P : real -> Prop) (Q : real -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem2267952 real P Q). Qed.
Lemma lem2267954 : term39 = term40.
Proof. exact (@lem2267953 term41 term42). Qed.
Lemma lem2267955 (r : real) : (term43 r) = (term44 r).
Proof. exact (eq_refl (term43 r)). Qed.
Lemma lem2267956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2267957 (r : real) : (term45 r) = (term46 r).
Proof. exact (MK_COMB (@lem2267956) (@lem2267955 r)). Qed.
Lemma lem2267958 (r : real) : (term47 r) = (term48 r).
Proof. exact (eq_refl (term47 r)). Qed.
Lemma lem2267959 (r : real) : (term49 r) = (term31 r).
Proof. exact (MK_COMB (@lem2267957 r) (@lem2267958 r)). Qed.
Lemma lem2267960 : term50 = term32.
Proof. exact (fun_ext (fun r : real => @lem2267959 r)). Qed.
Lemma lem2267961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2267962 : term39 = term33.
Proof. exact (MK_COMB (@lem2267961) (@lem2267960)). Qed.
Lemma lem2267963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2267964 : term51 = term52.
Proof. exact (MK_COMB (@lem2267963) (@lem2267962)). Qed.
Lemma lem2267965 (r : real) : (term43 r) = (term44 r).
Proof. exact (eq_refl (term43 r)). Qed.
Lemma lem2267966 : term53 = term41.
Proof. exact (fun_ext (fun r : real => @lem2267965 r)). Qed.
Lemma lem2267967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2267968 : term54 = term55.
Proof. exact (MK_COMB (@lem2267967) (@lem2267966)). Qed.
Lemma lem2267969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2267970 : term56 = term57.
Proof. exact (MK_COMB (@lem2267969) (@lem2267968)). Qed.
Lemma lem2267971 (r : real) : (term47 r) = (term48 r).
Proof. exact (eq_refl (term47 r)). Qed.
Lemma lem2267972 : term58 = term42.
Proof. exact (fun_ext (fun r : real => @lem2267971 r)). Qed.
Lemma lem2267973 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2267974 : term59 = term60.
Proof. exact (MK_COMB (@lem2267973) (@lem2267972)). Qed.
Lemma lem2267975 : term40 = term61.
Proof. exact (MK_COMB (@lem2267970) (@lem2267974)). Qed.
Lemma lem2267976 : (term39 = term40) = (term33 = term61).
Proof. exact (MK_COMB (@lem2267964) (@lem2267975)). Qed.
Lemma lem2267977 : term33 = term61.
Proof. exact (EQ_MP (@lem2267976) (@lem2267954)). Qed.
Lemma lem2268054 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem2268057 : term34 = term62.
Proof. exact (MK_COMB (@lem2268054) (@lem2267977)). Qed.
Lemma lem2268058 : term10 = term62.
Proof. exact (TRANS (@lem2267946) (@lem2268057)). Qed.
Lemma lem2268059 (h1 : term10) : term62.
Proof. exact (EQ_MP (@lem2268058) (@lem2267901 h1)). Qed.
Lemma lem2268077 (r : real) : (term48 r) = (term48 r).
Proof. exact (eq_refl (term48 r)). Qed.
Lemma lem2268078 : term42 = term42.
Proof. exact (fun_ext (fun r : real => @lem2268077 r)). Qed.
Lemma lem2268079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2268080 : term60 = term60.
Proof. exact (MK_COMB (@lem2268079) (@lem2268078)). Qed.
Lemma lem2268097 (r : real) : (term44 r) = (term44 r).
Proof. exact (eq_refl (term44 r)). Qed.
Lemma lem2268098 : term41 = term41.
Proof. exact (fun_ext (fun r : real => @lem2268097 r)). Qed.
Lemma lem2268099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2268100 : term55 = term55.
Proof. exact (MK_COMB (@lem2268099) (@lem2268098)). Qed.
Lemma lem2268101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2268102 : term57 = term57.
Proof. exact (MK_COMB (@lem2268101) (@lem2268100)). Qed.
Lemma lem2268103 : term61 = term61.
Proof. exact (MK_COMB (@lem2268102) (@lem2268080)). Qed.
Lemma lem2268112 (a : int) : ((term16 a) = a) = ((term16 a) = a).
Proof. exact (eq_refl ((term16 a) = a)). Qed.
Lemma lem2268113 : term17 = term17.
Proof. exact (fun_ext (fun a : int => @lem2268112 a)). Qed.
Lemma lem2268114 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2268115 : term18 = term18.
Proof. exact (MK_COMB (@lem2268114) (@lem2268113)). Qed.
Lemma lem2268116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2268117 : term19 = term19.
Proof. exact (MK_COMB (@lem2268116) (@lem2268115)). Qed.
Lemma lem2268118 : term62 = term62.
Proof. exact (MK_COMB (@lem2268117) (@lem2268103)). Qed.
Lemma lem2268119 (h1 : term10) : term62.
Proof. exact (EQ_MP (@lem2268118) (@lem2268059 h1)). Qed.
Lemma lem2268127 (x : int) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem2268128 (h1 : term10) : term61.
Proof. exact (proj2 (@lem2268119 h1)). Qed.
Lemma lem2268129 (h1 : term10) : term18.
Proof. exact (proj1 (@lem2268119 h1)). Qed.
Lemma lem2268131 (h1 : term10) : term55.
Proof. exact (proj1 (@lem2268128 h1)). Qed.
Lemma lem2268135 (x : int) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem2268137 (a : int) : ((term16 a) = a) = ((term16 a) = a).
Proof. exact (eq_refl ((term16 a) = a)). Qed.
Lemma lem2268138 : term17 = term17.
Proof. exact (fun_ext (fun a : int => @lem2268137 a)). Qed.
Lemma lem2268139 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2268141 : term18 = term18.
Proof. exact (MK_COMB (@lem2268139) (@lem2268138)). Qed.
Lemma lem2268142 (h1 : term10) : term18.
Proof. exact (EQ_MP (@lem2268141) (@lem2268129 h1)). Qed.
Lemma lem2268150 (r : real) : (term44 r) = (term44 r).
Proof. exact (eq_refl (term44 r)). Qed.
Lemma lem2268151 : term41 = term41.
Proof. exact (fun_ext (fun r : real => @lem2268150 r)). Qed.
Lemma lem2268152 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2268154 : term55 = term55.
Proof. exact (MK_COMB (@lem2268152) (@lem2268151)). Qed.
Lemma lem2268155 (h1 : term10) : term55.
Proof. exact (EQ_MP (@lem2268154) (@lem2268131 h1)). Qed.
Lemma lem2268169 (_28605 : int) (h1 : term10) : term63 _28605.
Proof. exact (@lem2268142 h1 _28605). Qed.
Lemma lem2268170 (_28605 : int) : (term63 _28605) = ((term16 _28605) = _28605).
Proof. exact (eq_refl (term63 _28605)). Qed.
Lemma lem2268172 (_28606 : real) (h1 : term10) : term43 _28606.
Proof. exact (@lem2268155 h1 _28606). Qed.
Lemma lem2268173 (_28606 : real) : (term43 _28606) = (term44 _28606).
Proof. exact (eq_refl (term43 _28606)). Qed.
Lemma lem2268179 (x : int) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem2268187 (_28606 : real) (h1 : term10) : term44 _28606.
Proof. exact (EQ_MP (@lem2268173 _28606) (@lem2268172 _28606 h1)). Qed.
Lemma lem2268214 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2268215 (_28612 : int) (_28613 : int) (h1 : _28612 = _28613) : _28612 = _28613.
Proof. exact (h1). Qed.
Lemma lem2268216 (_28612 : int) (_28613 : int) (h1 : _28612 = _28613) : (real_of_int _28612) = (real_of_int _28613).
Proof. exact (MK_COMB (@lem2268214) (@lem2268215 _28612 _28613 h1)). Qed.
Lemma lem2268217 (_28612 : int) (_28613 : int) : term64 _28612 _28613.
Proof. exact (fun h0 : _28612 = _28613 => @lem2268216 _28612 _28613 h0). Qed.
Lemma lem2268219 (a : Prop) (b : Prop) : (a -> b) = (term65 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2268220 (_28612 : int) (_28613 : int) : (term64 _28612 _28613) = (term66 _28612 _28613).
Proof. exact (@lem2268219 (_28612 = _28613) ((real_of_int _28612) = (real_of_int _28613))). Qed.
Lemma lem2268221 (_28612 : int) (_28613 : int) : term66 _28612 _28613.
Proof. exact (EQ_MP (@lem2268220 _28612 _28613) (@lem2268217 _28612 _28613)). Qed.
Lemma lem2268227 (_28605 : int) (h1 : term10) : (term16 _28605) = _28605.
Proof. exact (EQ_MP (@lem2268170 _28605) (@lem2268169 _28605 h1)). Qed.
Lemma lem2268228 (x : int) (h1 : term10) : (term16 x) = x.
Proof. exact (@lem2268227 x h1). Qed.
Lemma lem2268229 (x : int) (h1 : term10) : term67 x.
Proof. exact (fun h0 : term68 x => @lem2268228 x h1). Qed.
Lemma lem2268231 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2268232 (x : int) : (term67 x) = ((term16 x) = x).
Proof. exact (@lem2268231 ((term16 x) = x)). Qed.
Lemma lem2268233 (x : int) (h1 : term10) : (term16 x) = x.
Proof. exact (EQ_MP (@lem2268232 x) (@lem2268229 x h1)). Qed.
Lemma lem2268239 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2268240 (_28612 : int) (_28613 : int) : (term66 _28612 _28613) = (term70 _28612 _28613).
Proof. exact (@lem2268239 ((real_of_int _28612) = (real_of_int _28613)) (term71 _28612 _28613)). Qed.
Lemma lem2268250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2268251 (_28612 : int) (_28613 : int) : (term72 _28612 _28613) = (term73 _28612 _28613).
Proof. exact (MK_COMB (@lem2268250) (@lem2268240 _28612 _28613)). Qed.
Lemma lem2268261 (_28612 : int) (_28613 : int) : (term70 _28612 _28613) = (term70 _28612 _28613).
Proof. exact (eq_refl (term70 _28612 _28613)). Qed.
Lemma lem2268262 (_28612 : int) (_28613 : int) : ((term66 _28612 _28613) = (term70 _28612 _28613)) = ((term70 _28612 _28613) = (term70 _28612 _28613)).
Proof. exact (MK_COMB (@lem2268251 _28612 _28613) (@lem2268261 _28612 _28613)). Qed.
Lemma lem2268264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2268265 (x : Prop) : (x = x) = True.
Proof. exact (@lem2268264 Prop x). Qed.
Lemma lem2268266 (_28612 : int) (_28613 : int) : ((term70 _28612 _28613) = (term70 _28612 _28613)) = True.
Proof. exact (@lem2268265 (term70 _28612 _28613)). Qed.
Lemma lem2268267 (_28612 : int) (_28613 : int) : ((term66 _28612 _28613) = (term70 _28612 _28613)) = True.
Proof. exact (TRANS (@lem2268262 _28612 _28613) (@lem2268266 _28612 _28613)). Qed.
Lemma lem2268268 (_28612 : int) (_28613 : int) : True = ((term66 _28612 _28613) = (term70 _28612 _28613)).
Proof. exact (SYM (@lem2268267 _28612 _28613)). Qed.
Lemma lem2268269 (_28612 : int) (_28613 : int) : (term66 _28612 _28613) = (term70 _28612 _28613).
Proof. exact (EQ_MP (@lem2268268 _28612 _28613) (@lem0)). Qed.
Lemma lem2268270 (_28612 : int) (_28613 : int) : term70 _28612 _28613.
Proof. exact (EQ_MP (@lem2268269 _28612 _28613) (@lem2268221 _28612 _28613)). Qed.
Lemma lem2268272 (b : Prop) (a : Prop) : (a \/ b) = (term74 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2268273 (_28612 : int) (_28613 : int) : (term70 _28612 _28613) = (term75 _28612 _28613).
Proof. exact (@lem2268272 (term71 _28612 _28613) ((real_of_int _28612) = (real_of_int _28613))). Qed.
Lemma lem2268275 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2268276 (_28612 : int) (_28613 : int) : (term77 _28612 _28613) = (_28612 = _28613).
Proof. exact (@lem2268275 (_28612 = _28613)). Qed.
Lemma lem2268277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2268278 (_28612 : int) (_28613 : int) : (term78 _28612 _28613) = (term79 _28612 _28613).
Proof. exact (MK_COMB (@lem2268277) (@lem2268276 _28612 _28613)). Qed.
Lemma lem2268279 (_28612 : int) (_28613 : int) : ((real_of_int _28612) = (real_of_int _28613)) = ((real_of_int _28612) = (real_of_int _28613)).
Proof. exact (eq_refl ((real_of_int _28612) = (real_of_int _28613))). Qed.
Lemma lem2268280 (_28612 : int) (_28613 : int) : (term75 _28612 _28613) = (term64 _28612 _28613).
Proof. exact (MK_COMB (@lem2268278 _28612 _28613) (@lem2268279 _28612 _28613)). Qed.
Lemma lem2268281 (_28612 : int) (_28613 : int) : (term70 _28612 _28613) = (term64 _28612 _28613).
Proof. exact (TRANS (@lem2268273 _28612 _28613) (@lem2268280 _28612 _28613)). Qed.
Lemma lem2268284 (_28612 : int) (_28613 : int) : term64 _28612 _28613.
Proof. exact (EQ_MP (@lem2268281 _28612 _28613) (@lem2268270 _28612 _28613)). Qed.
Lemma lem2268285 (x : int) : term80 x.
Proof. exact (@lem2268284 (term16 x) x). Qed.
Lemma lem2268288 (x : int) (h1 : term10) : (term81 x) = (real_of_int x).
Proof. exact (@lem2268285 x (@lem2268233 x h1)). Qed.
Lemma lem2268289 (x : int) (h1 : term10) : term82 x.
Proof. exact (fun h0 : term83 x => @lem2268288 x h1). Qed.
Lemma lem2268291 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2268292 (x : int) : (term82 x) = ((term81 x) = (real_of_int x)).
Proof. exact (@lem2268291 ((term81 x) = (real_of_int x))). Qed.
Lemma lem2268293 (x : int) (h1 : term10) : (term81 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2268292 x) (@lem2268289 x h1)). Qed.
Lemma lem2268295 (b : Prop) (a : Prop) : (a \/ b) = (term74 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2268296 (_28606 : real) : (term44 _28606) = (term84 _28606).
Proof. exact (@lem2268295 (term85 _28606) (integer _28606)). Qed.
Lemma lem2268298 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2268299 (_28606 : real) : (term86 _28606) = ((term13 _28606) = _28606).
Proof. exact (@lem2268298 ((term13 _28606) = _28606)). Qed.
Lemma lem2268300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2268301 (_28606 : real) : (term87 _28606) = (term88 _28606).
Proof. exact (MK_COMB (@lem2268300) (@lem2268299 _28606)). Qed.
Lemma lem2268302 (_28606 : real) : (integer _28606) = (integer _28606).
Proof. exact (eq_refl (integer _28606)). Qed.
Lemma lem2268303 (_28606 : real) : (term84 _28606) = (term89 _28606).
Proof. exact (MK_COMB (@lem2268301 _28606) (@lem2268302 _28606)). Qed.
Lemma lem2268304 (_28606 : real) : (term44 _28606) = (term89 _28606).
Proof. exact (TRANS (@lem2268296 _28606) (@lem2268303 _28606)). Qed.
Lemma lem2268307 (_28606 : real) (h1 : term10) : term89 _28606.
Proof. exact (EQ_MP (@lem2268304 _28606) (@lem2268187 _28606 h1)). Qed.
Lemma lem2268308 (x : int) (h1 : term10) : term90 x.
Proof. exact (@lem2268307 (real_of_int x) h1). Qed.
Lemma lem2268311 (x : int) (h1 : term10) : term20 x.
Proof. exact (@lem2268308 x h1 (@lem2268293 x h1)). Qed.
Lemma lem2268312 (x : int) (h1 : term10) : term91 x.
Proof. exact (fun h0 : term27 x => @lem2268311 x h1). Qed.
Lemma lem2268314 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2268315 (x : int) : (term91 x) = (term20 x).
Proof. exact (@lem2268314 (term20 x)). Qed.
Lemma lem2268316 (x : int) (h1 : term10) : term20 x.
Proof. exact (EQ_MP (@lem2268315 x) (@lem2268312 x h1)). Qed.
Lemma lem2268319 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2268321 (x : int) : (term27 x) = (term92 x).
Proof. exact (@lem2268319 (term20 x)). Qed.
Lemma lem2268324 (x : int) (h1 : term27 x) : term92 x.
Proof. exact (EQ_MP (@lem2268321 x) (@lem2268179 x h1)). Qed.
Lemma lem2268327 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (@lem2268324 x h1 (@lem2268316 x h2)). Qed.
Lemma lem2268328 (x : int) (h1 : term27 x) (h2 : term10) : term93.
Proof. exact (fun h0 : ~ False => @lem2268327 x h1 h2). Qed.
Lemma lem2268330 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2268331 : term93 = False.
Proof. exact (@lem2268330 False). Qed.
Lemma lem2268332 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem2268331) (@lem2268328 x h1 h2)). Qed.
Lemma lem2268333 (x : int) (h1 : term27 x) (h2 : term10) : (term27 x) = False.
Proof. exact (prop_ext (fun h3 : term27 x => @lem2268332 x h1 h2) (fun h3 : False => @lem2268179 x h1)). Qed.
Lemma lem2268334 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem2268333 x h1 h2) (@lem2268179 x h1)). Qed.
Lemma lem2268335 (x : int) (h1 : term27 x) (h2 : term10) : (term27 x) = False.
Proof. exact (prop_ext (fun h3 : term27 x => @lem2268334 x h1 h2) (fun h3 : False => @lem2268135 x h1)). Qed.
Lemma lem2268336 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem2268335 x h1 h2) (@lem2268135 x h1)). Qed.
Lemma lem2268337 (x : int) (h1 : term27 x) (h2 : term10) : (term27 x) = False.
Proof. exact (prop_ext (fun h3 : term27 x => @lem2268336 x h1 h2) (fun h3 : False => @lem2268135 x h1)). Qed.
Lemma lem2268338 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem2268337 x h1 h2) (@lem2268135 x h1)). Qed.
Lemma lem2268339 (x : int) (h1 : term27 x) (h2 : term10) : (term27 x) = False.
Proof. exact (prop_ext (fun h3 : term27 x => @lem2268338 x h1 h2) (fun h3 : False => @lem2268127 x h1)). Qed.
Lemma lem2268340 (x : int) (h1 : term27 x) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem2268339 x h1 h2) (@lem2268127 x h1)). Qed.
Lemma lem2268341 (h1 : term3) (h2 : term10) : False.
Proof. exact (ex_elim (@lem2267921 h1) (fun x : int => fun h0 : term29 x => @lem2268340 x h0 h2)). Qed.
Lemma lem2268342 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2268341 h1 h0). Qed.
Lemma lem2268343 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2268344 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem2268343) (@lem2268342 h1)). Qed.
Lemma lem2268345 : term12.
Proof. exact (fun h0 : term3 => @lem2268344 h0). Qed.
Lemma lem2268346 : term4.
Proof. exact (EQ_MP (@lem2267899) (@lem2268345)). Qed.
Lemma lem2268348 : term4.
Proof. exact (@lem2267820 (@lem2268346)). Qed.
Lemma lem2268349 (h1 : term3) : term8.
Proof. exact (@lem2268348 (@lem2267805 h1)). Qed.
Lemma lem2268350 (h1 : term3) : False.
Proof. exact (@lem2268349 h1 (@lem2267738)). Qed.
Lemma lem2268351 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2268350 h1) (fun h2 : False => @lem2267805 h1)). Qed.
Lemma lem2268352 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2268351 h1) (@lem2267805 h1)). Qed.
Lemma lem2268353 : term2.
Proof. exact (fun h0 : term3 => @lem2268352 h0). Qed.
Lemma lem2268354 : term1.
Proof. exact (EQ_MP (@lem2267804) (@lem2268353)). Qed.
