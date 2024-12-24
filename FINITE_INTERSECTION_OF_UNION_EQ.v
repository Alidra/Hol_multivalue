Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_UNION_EQ_term_abbrevs.
Require Import COMPL_COMPL_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_INTERSECTION_OF_COMPLEMENT_spec.
Require Import FINITE_UNION_OF_INTER_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem4890890 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4890891 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4890904 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4890905 {_112654 : Type'} (P : type686 _112654) : ((term3 _112654 P) = (term4 _112654 P)) = (term5 _112654 P).
Proof. exact (@lem4890904 ((term3 _112654 P) = (term4 _112654 P))). Qed.
Lemma lem4890906 {_112654 : Type'} (P : type686 _112654) : (term5 _112654 P) = ((term3 _112654 P) = (term4 _112654 P)).
Proof. exact (SYM (@lem4890905 _112654 P)). Qed.
Lemma lem4890907 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term6 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4890908 {_112654 : Type'} : term7 _112654.
Proof. exact (@lem3270825 _112654). Qed.
Lemma lem4890912 {_112654 : Type'} (P : type686 _112654) (h1 : term8 _112654 P) : term8 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4890913 {_112654 : Type'} (P : type686 _112654) : term9 _112654 P.
Proof. exact (fun h0 : term8 _112654 P => @lem4890912 _112654 P h0). Qed.
Lemma lem4890914 {_112654 : Type'} (P : type686 _112654) (h1 : term9 _112654 P) : term9 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4890915 {_112654 : Type'} (P : type686 _112654) (h1 : term8 _112654 P) : term8 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4890916 {_112654 : Type'} (P : type686 _112654) (h1 : term8 _112654 P) (h2 : term9 _112654 P) : term8 _112654 P.
Proof. exact (@lem4890914 _112654 P h2 (@lem4890915 _112654 P h1)). Qed.
Lemma lem4890917 {_112654 : Type'} (P : type686 _112654) (h1 : term8 _112654 P) : term10 _112654 P.
Proof. exact (fun h0 : term9 _112654 P => @lem4890916 _112654 P h1 h0). Qed.
Lemma lem4890918 {_112654 : Type'} (P : type686 _112654) (h1 : term9 _112654 P) : term9 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4890919 {_112654 : Type'} (P : type686 _112654) (h1 : term8 _112654 P) (h2 : term9 _112654 P) : term8 _112654 P.
Proof. exact (@lem4890917 _112654 P h1 (@lem4890918 _112654 P h2)). Qed.
Lemma lem4890920 {_112654 : Type'} (P : type686 _112654) (h1 : term9 _112654 P) : term9 _112654 P.
Proof. exact (fun h0 : term8 _112654 P => @lem4890919 _112654 P h0 h1). Qed.
Lemma lem4890921 {_112654 : Type'} (P : type686 _112654) : term11 _112654 P.
Proof. exact (fun h0 : term9 _112654 P => @lem4890920 _112654 P h0). Qed.
Lemma lem4890924 {_112654 : Type'} (P : type686 _112654) : term9 _112654 P.
Proof. exact (@lem4890921 _112654 P (@lem4890913 _112654 P)). Qed.
Lemma lem4890925 {_112654 : Type'} (P : type686 _112654) : term9 _112654 P.
Proof. exact (@lem4890924 _112654 P). Qed.
Lemma lem4890941 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4890942 {_112654 : Type'} : (term12 _112654) = (term13 _112654).
Proof. exact (@lem4890941 (term7 _112654)). Qed.
Lemma lem4890947 {_112654 : Type'} (P : type686 _112654) : (term14 _112654 P) = (term14 _112654 P).
Proof. exact (eq_refl (term14 _112654 P)). Qed.
Lemma lem4890948 {_112654 : Type'} (P : type686 _112654) : (term8 _112654 P) = (term15 _112654 P).
Proof. exact (MK_COMB (@lem4890947 _112654 P) (@lem4890942 _112654)). Qed.
Lemma lem4890951 {_112654 : Type'} : (term16 _112654) = (term17 _112654).
Proof. exact (fun_ext (fun P : type686 _112654 => @lem4890948 _112654 P)). Qed.
Lemma lem4890952 {_112654 : Type'} : (@all ((_112654 -> Prop) -> Prop)) = (@all ((_112654 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112654 -> Prop) -> Prop))). Qed.
Lemma lem4890961 {_112654 : Type'} : (term18 _112654) = (term19 _112654).
Proof. exact (MK_COMB (@lem4890952 _112654) (@lem4890951 _112654)). Qed.
Lemma lem4890962 {_112654 : Type'} (s : _112654 -> Prop) : ((term1 _112654 s) = s) = ((term1 _112654 s) = s).
Proof. exact (eq_refl ((term1 _112654 s) = s)). Qed.
Lemma lem4890963 {_112654 : Type'} : (term20 _112654) = (term20 _112654).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4890962 _112654 s)). Qed.
Lemma lem4890964 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4890965 {_112654 : Type'} : (term7 _112654) = (term7 _112654).
Proof. exact (MK_COMB (@lem4890964 _112654) (@lem4890963 _112654)). Qed.
Lemma lem4890966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890967 {_112654 : Type'} : (term13 _112654) = (term13 _112654).
Proof. exact (MK_COMB (@lem4890966) (@lem4890965 _112654)). Qed.
Lemma lem4890968 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4890969 {_112654 : Type'} (P : type686 _112654) : (term21 _112654 P) = (term21 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4890968 _112654 P s)). Qed.
Lemma lem4890970 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4890971 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (MK_COMB (@lem4890970 _112654) (@lem4890969 _112654 P)). Qed.
Lemma lem4890972 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term22 _112654 P s) = (term22 _112654 P s).
Proof. exact (eq_refl (term22 _112654 P s)). Qed.
Lemma lem4890973 {_112654 : Type'} (P : type686 _112654) : (term23 _112654 P) = (term23 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4890972 _112654 P s)). Qed.
Lemma lem4890974 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4890975 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term3 _112654 P).
Proof. exact (MK_COMB (@lem4890974 _112654) (@lem4890973 _112654 P)). Qed.
Lemma lem4890976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4890977 {_112654 : Type'} (P : type686 _112654) : (term24 _112654 P) = (term24 _112654 P).
Proof. exact (MK_COMB (@lem4890976) (@lem4890975 _112654 P)). Qed.
Lemma lem4890978 {_112654 : Type'} (P : type686 _112654) : ((term3 _112654 P) = (term4 _112654 P)) = ((term3 _112654 P) = (term4 _112654 P)).
Proof. exact (MK_COMB (@lem4890977 _112654 P) (@lem4890971 _112654 P)). Qed.
Lemma lem4890979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4890980 {_112654 : Type'} (P : type686 _112654) : (term6 _112654 P) = (term6 _112654 P).
Proof. exact (MK_COMB (@lem4890979) (@lem4890978 _112654 P)). Qed.
Lemma lem4890981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4890982 {_112654 : Type'} (P : type686 _112654) : (term14 _112654 P) = (term14 _112654 P).
Proof. exact (MK_COMB (@lem4890981) (@lem4890980 _112654 P)). Qed.
Lemma lem4890983 {_112654 : Type'} (P : type686 _112654) : (term15 _112654 P) = (term15 _112654 P).
Proof. exact (MK_COMB (@lem4890982 _112654 P) (@lem4890967 _112654)). Qed.
Lemma lem4890984 {_112654 : Type'} : (term17 _112654) = (term17 _112654).
Proof. exact (fun_ext (fun P : type686 _112654 => @lem4890983 _112654 P)). Qed.
Lemma lem4890985 {_112654 : Type'} : (@all ((_112654 -> Prop) -> Prop)) = (@all ((_112654 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112654 -> Prop) -> Prop))). Qed.
Lemma lem4890986 {_112654 : Type'} : (term19 _112654) = (term19 _112654).
Proof. exact (MK_COMB (@lem4890985 _112654) (@lem4890984 _112654)). Qed.
Lemma lem4891015 {_112654 : Type'} : (term18 _112654) = (term19 _112654).
Proof. exact (TRANS (@lem4890961 _112654) (@lem4890986 _112654)). Qed.
Lemma lem4891016 {_112654 : Type'} : (term19 _112654) = (term18 _112654).
Proof. exact (SYM (@lem4891015 _112654)). Qed.
Lemma lem4891017 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term6 _112654 P.
Proof. exact (h1). Qed.
Lemma lem4891018 {_112654 : Type'} (h1 : term7 _112654) : term7 _112654.
Proof. exact (h1). Qed.
Lemma lem4891020 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term22 _112654 P s) = (term22 _112654 P s).
Proof. exact (eq_refl (term22 _112654 P s)). Qed.
Lemma lem4891021 {_112654 : Type'} (P : type686 _112654) : (term25 _112654 P) = (term26 _112654 P).
Proof. exact (@lem18392 (_112654 -> Prop) P). Qed.
Lemma lem4891022 {_112654 : Type'} (P : type686 _112654) : (term27 _112654 P) = (term28 _112654 P).
Proof. exact (@lem4891021 _112654 (term23 _112654 P)). Qed.
Lemma lem4891023 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term29 _112654 P s) = (term22 _112654 P s).
Proof. exact (eq_refl (term29 _112654 P s)). Qed.
Lemma lem4891024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4891026 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term30 _112654 P s) = (term31 _112654 P s).
Proof. exact (MK_COMB (@lem4891024) (@lem4891023 _112654 P s)). Qed.
Lemma lem4891027 {_112654 : Type'} (P : type686 _112654) : (term32 _112654 P) = (term33 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891026 _112654 P s)). Qed.
Lemma lem4891028 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891029 {_112654 : Type'} (P : type686 _112654) : (term28 _112654 P) = (term34 _112654 P).
Proof. exact (MK_COMB (@lem4891028 _112654) (@lem4891027 _112654 P)). Qed.
Lemma lem4891030 {_112654 : Type'} (P : type686 _112654) : (term27 _112654 P) = (term34 _112654 P).
Proof. exact (TRANS (@lem4891022 _112654 P) (@lem4891029 _112654 P)). Qed.
Lemma lem4891031 {_112654 : Type'} (P : type686 _112654) : (term23 _112654 P) = (term23 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891020 _112654 P s)). Qed.
Lemma lem4891032 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891033 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term3 _112654 P).
Proof. exact (MK_COMB (@lem4891032 _112654) (@lem4891031 _112654 P)). Qed.
Lemma lem4891035 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4891036 {_112654 : Type'} (P : type686 _112654) : (term25 _112654 P) = (term26 _112654 P).
Proof. exact (@lem18392 (_112654 -> Prop) P). Qed.
Lemma lem4891037 {_112654 : Type'} (P : type686 _112654) : (term35 _112654 P) = (term36 _112654 P).
Proof. exact (@lem4891036 _112654 (term21 _112654 P)). Qed.
Lemma lem4891038 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term37 _112654 P s) = (P s).
Proof. exact (eq_refl (term37 _112654 P s)). Qed.
Lemma lem4891039 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4891041 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term38 _112654 P s) = (term39 _112654 P s).
Proof. exact (MK_COMB (@lem4891039) (@lem4891038 _112654 P s)). Qed.
Lemma lem4891042 {_112654 : Type'} (P : type686 _112654) : (term40 _112654 P) = (term41 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891041 _112654 P s)). Qed.
Lemma lem4891043 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891044 {_112654 : Type'} (P : type686 _112654) : (term36 _112654 P) = (term26 _112654 P).
Proof. exact (MK_COMB (@lem4891043 _112654) (@lem4891042 _112654 P)). Qed.
Lemma lem4891045 {_112654 : Type'} (P : type686 _112654) : (term35 _112654 P) = (term26 _112654 P).
Proof. exact (TRANS (@lem4891037 _112654 P) (@lem4891044 _112654 P)). Qed.
Lemma lem4891046 {_112654 : Type'} (P : type686 _112654) : (term21 _112654 P) = (term21 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891035 _112654 P s)). Qed.
Lemma lem4891047 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891048 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (MK_COMB (@lem4891047 _112654) (@lem4891046 _112654 P)). Qed.
Lemma lem4891049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891050 {_112654 : Type'} (P : type686 _112654) : (term42 _112654 P) = (term43 _112654 P).
Proof. exact (MK_COMB (@lem4891049) (@lem4891030 _112654 P)). Qed.
Lemma lem4891051 {_112654 : Type'} (P : type686 _112654) : (term44 _112654 P) = (term45 _112654 P).
Proof. exact (MK_COMB (@lem4891050 _112654 P) (@lem4891048 _112654 P)). Qed.
Lemma lem4891052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891053 {_112654 : Type'} (P : type686 _112654) : (term46 _112654 P) = (term46 _112654 P).
Proof. exact (MK_COMB (@lem4891052) (@lem4891033 _112654 P)). Qed.
Lemma lem4891054 {_112654 : Type'} (P : type686 _112654) : (term47 _112654 P) = (term48 _112654 P).
Proof. exact (MK_COMB (@lem4891053 _112654 P) (@lem4891045 _112654 P)). Qed.
Lemma lem4891055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891056 {_112654 : Type'} (P : type686 _112654) : (term49 _112654 P) = (term50 _112654 P).
Proof. exact (MK_COMB (@lem4891055) (@lem4891054 _112654 P)). Qed.
Lemma lem4891057 {_112654 : Type'} (P : type686 _112654) : (term51 _112654 P) = (term52 _112654 P).
Proof. exact (MK_COMB (@lem4891056 _112654 P) (@lem4891051 _112654 P)). Qed.
Lemma lem4891058 {_112654 : Type'} (P : type686 _112654) : (term6 _112654 P) = (term51 _112654 P).
Proof. exact (@lem17646 (term3 _112654 P) (term4 _112654 P)). Qed.
Lemma lem4891059 {_112654 : Type'} (P : type686 _112654) : (term6 _112654 P) = (term52 _112654 P).
Proof. exact (TRANS (@lem4891058 _112654 P) (@lem4891057 _112654 P)). Qed.
Lemma lem4891078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term53 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4891079 {_112654 : Type'} (P : Prop) (Q : type686 _112654) : (term55 _112654 P Q) = (term56 _112654 P Q).
Proof. exact (@lem4891078 (_112654 -> Prop) P Q). Qed.
Lemma lem4891080 {_112654 : Type'} (P : type686 _112654) : (term57 _112654 P) = (term58 _112654 P).
Proof. exact (@lem4891079 _112654 (term3 _112654 P) (term41 _112654 P)). Qed.
Lemma lem4891081 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term59 _112654 P s) = (term39 _112654 P s).
Proof. exact (eq_refl (term59 _112654 P s)). Qed.
Lemma lem4891082 {_112654 : Type'} (P : type686 _112654) : (term60 _112654 P) = (term41 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891081 _112654 P s)). Qed.
Lemma lem4891083 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891084 {_112654 : Type'} (P : type686 _112654) : (term61 _112654 P) = (term26 _112654 P).
Proof. exact (MK_COMB (@lem4891083 _112654) (@lem4891082 _112654 P)). Qed.
Lemma lem4891085 {_112654 : Type'} (P : type686 _112654) : (term46 _112654 P) = (term46 _112654 P).
Proof. exact (eq_refl (term46 _112654 P)). Qed.
Lemma lem4891086 {_112654 : Type'} (P : type686 _112654) : (term57 _112654 P) = (term48 _112654 P).
Proof. exact (MK_COMB (@lem4891085 _112654 P) (@lem4891084 _112654 P)). Qed.
Lemma lem4891087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4891088 {_112654 : Type'} (P : type686 _112654) : (term62 _112654 P) = (term63 _112654 P).
Proof. exact (MK_COMB (@lem4891087) (@lem4891086 _112654 P)). Qed.
Lemma lem4891089 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term59 _112654 P s) = (term39 _112654 P s).
Proof. exact (eq_refl (term59 _112654 P s)). Qed.
Lemma lem4891090 {_112654 : Type'} (P : type686 _112654) : (term46 _112654 P) = (term46 _112654 P).
Proof. exact (eq_refl (term46 _112654 P)). Qed.
Lemma lem4891091 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term64 _112654 P s) = (term65 _112654 P s).
Proof. exact (MK_COMB (@lem4891090 _112654 P) (@lem4891089 _112654 P s)). Qed.
Lemma lem4891092 {_112654 : Type'} (P : type686 _112654) : (term66 _112654 P) = (term67 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891091 _112654 P s)). Qed.
Lemma lem4891093 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891094 {_112654 : Type'} (P : type686 _112654) : (term58 _112654 P) = (term68 _112654 P).
Proof. exact (MK_COMB (@lem4891093 _112654) (@lem4891092 _112654 P)). Qed.
Lemma lem4891095 {_112654 : Type'} (P : type686 _112654) : ((term57 _112654 P) = (term58 _112654 P)) = ((term48 _112654 P) = (term68 _112654 P)).
Proof. exact (MK_COMB (@lem4891088 _112654 P) (@lem4891094 _112654 P)). Qed.
Lemma lem4891096 {_112654 : Type'} (P : type686 _112654) : (term48 _112654 P) = (term68 _112654 P).
Proof. exact (EQ_MP (@lem4891095 _112654 P) (@lem4891080 _112654 P)). Qed.
Lemma lem4891097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891098 {_112654 : Type'} (P : type686 _112654) : (term50 _112654 P) = (term69 _112654 P).
Proof. exact (MK_COMB (@lem4891097) (@lem4891096 _112654 P)). Qed.
Lemma lem4891100 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4891101 {_112654 : Type'} (P : type686 _112654) (Q : Prop) : (term72 _112654 P Q) = (term73 _112654 P Q).
Proof. exact (@lem4891100 (_112654 -> Prop) P Q). Qed.
Lemma lem4891102 {_112654 : Type'} (P : type686 _112654) : (term74 _112654 P) = (term75 _112654 P).
Proof. exact (@lem4891101 _112654 (term33 _112654 P) (term4 _112654 P)). Qed.
Lemma lem4891103 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term76 _112654 P s) = (term31 _112654 P s).
Proof. exact (eq_refl (term76 _112654 P s)). Qed.
Lemma lem4891104 {_112654 : Type'} (P : type686 _112654) : (term77 _112654 P) = (term33 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891103 _112654 P s)). Qed.
Lemma lem4891105 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891106 {_112654 : Type'} (P : type686 _112654) : (term78 _112654 P) = (term34 _112654 P).
Proof. exact (MK_COMB (@lem4891105 _112654) (@lem4891104 _112654 P)). Qed.
Lemma lem4891107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891108 {_112654 : Type'} (P : type686 _112654) : (term79 _112654 P) = (term43 _112654 P).
Proof. exact (MK_COMB (@lem4891107) (@lem4891106 _112654 P)). Qed.
Lemma lem4891109 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (eq_refl (term4 _112654 P)). Qed.
Lemma lem4891110 {_112654 : Type'} (P : type686 _112654) : (term74 _112654 P) = (term45 _112654 P).
Proof. exact (MK_COMB (@lem4891108 _112654 P) (@lem4891109 _112654 P)). Qed.
Lemma lem4891111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4891112 {_112654 : Type'} (P : type686 _112654) : (term80 _112654 P) = (term81 _112654 P).
Proof. exact (MK_COMB (@lem4891111) (@lem4891110 _112654 P)). Qed.
Lemma lem4891113 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term76 _112654 P s) = (term31 _112654 P s).
Proof. exact (eq_refl (term76 _112654 P s)). Qed.
Lemma lem4891114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891115 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term82 _112654 P s) = (term83 _112654 P s).
Proof. exact (MK_COMB (@lem4891114) (@lem4891113 _112654 P s)). Qed.
Lemma lem4891116 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (eq_refl (term4 _112654 P)). Qed.
Lemma lem4891117 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term84 _112654 s P) = (term85 _112654 s P).
Proof. exact (MK_COMB (@lem4891115 _112654 P s) (@lem4891116 _112654 P)). Qed.
Lemma lem4891118 {_112654 : Type'} (P : type686 _112654) : (term86 _112654 P) = (term87 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891117 _112654 s P)). Qed.
Lemma lem4891119 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891120 {_112654 : Type'} (P : type686 _112654) : (term75 _112654 P) = (term88 _112654 P).
Proof. exact (MK_COMB (@lem4891119 _112654) (@lem4891118 _112654 P)). Qed.
Lemma lem4891121 {_112654 : Type'} (P : type686 _112654) : ((term74 _112654 P) = (term75 _112654 P)) = ((term45 _112654 P) = (term88 _112654 P)).
Proof. exact (MK_COMB (@lem4891112 _112654 P) (@lem4891120 _112654 P)). Qed.
Lemma lem4891122 {_112654 : Type'} (P : type686 _112654) : (term45 _112654 P) = (term88 _112654 P).
Proof. exact (EQ_MP (@lem4891121 _112654 P) (@lem4891102 _112654 P)). Qed.
Lemma lem4891123 {_112654 : Type'} (P : type686 _112654) : (term52 _112654 P) = (term89 _112654 P).
Proof. exact (MK_COMB (@lem4891098 _112654 P) (@lem4891122 _112654 P)). Qed.
Lemma lem4891125 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4891126 {_112654 : Type'} (P : type686 _112654) (Q : type686 _112654) : (term92 _112654 P Q) = (term93 _112654 P Q).
Proof. exact (@lem4891125 (_112654 -> Prop) P Q). Qed.
Lemma lem4891127 {_112654 : Type'} (P : type686 _112654) : (term94 _112654 P) = (term95 _112654 P).
Proof. exact (@lem4891126 _112654 (term67 _112654 P) (term87 _112654 P)). Qed.
Lemma lem4891128 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term96 _112654 P s) = (term65 _112654 P s).
Proof. exact (eq_refl (term96 _112654 P s)). Qed.
Lemma lem4891129 {_112654 : Type'} (P : type686 _112654) : (term97 _112654 P) = (term67 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891128 _112654 P s)). Qed.
Lemma lem4891130 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891131 {_112654 : Type'} (P : type686 _112654) : (term98 _112654 P) = (term68 _112654 P).
Proof. exact (MK_COMB (@lem4891130 _112654) (@lem4891129 _112654 P)). Qed.
Lemma lem4891132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891133 {_112654 : Type'} (P : type686 _112654) : (term99 _112654 P) = (term69 _112654 P).
Proof. exact (MK_COMB (@lem4891132) (@lem4891131 _112654 P)). Qed.
Lemma lem4891134 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term100 _112654 P s) = (term85 _112654 s P).
Proof. exact (eq_refl (term100 _112654 P s)). Qed.
Lemma lem4891135 {_112654 : Type'} (P : type686 _112654) : (term101 _112654 P) = (term87 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891134 _112654 s P)). Qed.
Lemma lem4891136 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891137 {_112654 : Type'} (P : type686 _112654) : (term102 _112654 P) = (term88 _112654 P).
Proof. exact (MK_COMB (@lem4891136 _112654) (@lem4891135 _112654 P)). Qed.
Lemma lem4891138 {_112654 : Type'} (P : type686 _112654) : (term94 _112654 P) = (term89 _112654 P).
Proof. exact (MK_COMB (@lem4891133 _112654 P) (@lem4891137 _112654 P)). Qed.
Lemma lem4891139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4891140 {_112654 : Type'} (P : type686 _112654) : (term103 _112654 P) = (term104 _112654 P).
Proof. exact (MK_COMB (@lem4891139) (@lem4891138 _112654 P)). Qed.
Lemma lem4891141 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term96 _112654 P s) = (term65 _112654 P s).
Proof. exact (eq_refl (term96 _112654 P s)). Qed.
Lemma lem4891142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891143 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term105 _112654 P s) = (term106 _112654 P s).
Proof. exact (MK_COMB (@lem4891142) (@lem4891141 _112654 P s)). Qed.
Lemma lem4891144 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term100 _112654 P s) = (term85 _112654 s P).
Proof. exact (eq_refl (term100 _112654 P s)). Qed.
Lemma lem4891145 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term107 _112654 P s) = (term108 _112654 s P).
Proof. exact (MK_COMB (@lem4891143 _112654 P s) (@lem4891144 _112654 s P)). Qed.
Lemma lem4891146 {_112654 : Type'} (P : type686 _112654) : (term109 _112654 P) = (term110 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891145 _112654 s P)). Qed.
Lemma lem4891147 {_112654 : Type'} : (@ex (_112654 -> Prop)) = (@ex (_112654 -> Prop)).
Proof. exact (eq_refl (@ex (_112654 -> Prop))). Qed.
Lemma lem4891148 {_112654 : Type'} (P : type686 _112654) : (term95 _112654 P) = (term111 _112654 P).
Proof. exact (MK_COMB (@lem4891147 _112654) (@lem4891146 _112654 P)). Qed.
Lemma lem4891149 {_112654 : Type'} (P : type686 _112654) : ((term94 _112654 P) = (term95 _112654 P)) = ((term89 _112654 P) = (term111 _112654 P)).
Proof. exact (MK_COMB (@lem4891140 _112654 P) (@lem4891148 _112654 P)). Qed.
Lemma lem4891150 {_112654 : Type'} (P : type686 _112654) : (term89 _112654 P) = (term111 _112654 P).
Proof. exact (EQ_MP (@lem4891149 _112654 P) (@lem4891127 _112654 P)). Qed.
Lemma lem4891152 {_112654 : Type'} (P : type686 _112654) : (term52 _112654 P) = (term111 _112654 P).
Proof. exact (TRANS (@lem4891123 _112654 P) (@lem4891150 _112654 P)). Qed.
Lemma lem4891153 {_112654 : Type'} (P : type686 _112654) : (term6 _112654 P) = (term111 _112654 P).
Proof. exact (TRANS (@lem4891059 _112654 P) (@lem4891152 _112654 P)). Qed.
Lemma lem4891154 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term111 _112654 P.
Proof. exact (EQ_MP (@lem4891153 _112654 P) (@lem4891017 _112654 P h1)). Qed.
Lemma lem4891155 {_112654 : Type'} (s : _112654 -> Prop) : ((term1 _112654 s) = s) = ((term1 _112654 s) = s).
Proof. exact (eq_refl ((term1 _112654 s) = s)). Qed.
Lemma lem4891156 {_112654 : Type'} : (term20 _112654) = (term20 _112654).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891155 _112654 s)). Qed.
Lemma lem4891157 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891166 {_112654 : Type'} : (term7 _112654) = (term7 _112654).
Proof. exact (MK_COMB (@lem4891157 _112654) (@lem4891156 _112654)). Qed.
Lemma lem4891167 {_112654 : Type'} (h1 : term7 _112654) : term7 _112654.
Proof. exact (EQ_MP (@lem4891166 _112654) (@lem4891018 _112654 h1)). Qed.
Lemma lem4891168 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term108 _112654 s P) : term108 _112654 s P.
Proof. exact (h1). Qed.
Lemma lem4891181 {_112654 : Type'} (s : _112654 -> Prop) : ((term1 _112654 s) = s) = ((term1 _112654 s) = s).
Proof. exact (eq_refl ((term1 _112654 s) = s)). Qed.
Lemma lem4891182 {_112654 : Type'} : (term20 _112654) = (term20 _112654).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891181 _112654 s)). Qed.
Lemma lem4891183 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891184 {_112654 : Type'} : (term7 _112654) = (term7 _112654).
Proof. exact (MK_COMB (@lem4891183 _112654) (@lem4891182 _112654)). Qed.
Lemma lem4891185 {_112654 : Type'} (h1 : term7 _112654) : term7 _112654.
Proof. exact (EQ_MP (@lem4891184 _112654) (@lem4891167 _112654 h1)). Qed.
Lemma lem4891188 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4891189 {_112654 : Type'} (P : type686 _112654) : (term21 _112654 P) = (term21 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891188 _112654 P s)). Qed.
Lemma lem4891190 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891191 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (MK_COMB (@lem4891190 _112654) (@lem4891189 _112654 P)). Qed.
Lemma lem4891202 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term83 _112654 P s) = (term83 _112654 P s).
Proof. exact (eq_refl (term83 _112654 P s)). Qed.
Lemma lem4891203 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term85 _112654 s P) = (term85 _112654 s P).
Proof. exact (MK_COMB (@lem4891202 _112654 P s) (@lem4891191 _112654 P)). Qed.
Lemma lem4891208 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term39 _112654 P s) = (term39 _112654 P s).
Proof. exact (eq_refl (term39 _112654 P s)). Qed.
Lemma lem4891215 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term22 _112654 P s) = (term22 _112654 P s).
Proof. exact (eq_refl (term22 _112654 P s)). Qed.
Lemma lem4891216 {_112654 : Type'} (P : type686 _112654) : (term23 _112654 P) = (term23 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891215 _112654 P s)). Qed.
Lemma lem4891217 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891218 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term3 _112654 P).
Proof. exact (MK_COMB (@lem4891217 _112654) (@lem4891216 _112654 P)). Qed.
Lemma lem4891219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891220 {_112654 : Type'} (P : type686 _112654) : (term46 _112654 P) = (term46 _112654 P).
Proof. exact (MK_COMB (@lem4891219) (@lem4891218 _112654 P)). Qed.
Lemma lem4891221 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term65 _112654 P s) = (term65 _112654 P s).
Proof. exact (MK_COMB (@lem4891220 _112654 P) (@lem4891208 _112654 P s)). Qed.
Lemma lem4891222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891223 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term106 _112654 P s) = (term106 _112654 P s).
Proof. exact (MK_COMB (@lem4891222) (@lem4891221 _112654 P s)). Qed.
Lemma lem4891224 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) : (term108 _112654 s P) = (term108 _112654 s P).
Proof. exact (MK_COMB (@lem4891223 _112654 P s) (@lem4891203 _112654 s P)). Qed.
Lemma lem4891225 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term108 _112654 s P) : term108 _112654 s P.
Proof. exact (EQ_MP (@lem4891224 _112654 s P) (@lem4891168 _112654 s P h1)). Qed.
Lemma lem4891226 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term65 _112654 P s.
Proof. exact (h1). Qed.
Lemma lem4891227 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term85 _112654 s P.
Proof. exact (h1). Qed.
Lemma lem4891229 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term3 _112654 P.
Proof. exact (proj1 (@lem4891226 _112654 P s h1)). Qed.
Lemma lem4891230 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term4 _112654 P.
Proof. exact (proj2 (@lem4891227 _112654 s P h1)). Qed.
Lemma lem4891233 {_112654 : Type'} (s : _112654 -> Prop) : ((term1 _112654 s) = s) = ((term1 _112654 s) = s).
Proof. exact (eq_refl ((term1 _112654 s) = s)). Qed.
Lemma lem4891234 {_112654 : Type'} : (term20 _112654) = (term20 _112654).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891233 _112654 s)). Qed.
Lemma lem4891235 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891237 {_112654 : Type'} : (term7 _112654) = (term7 _112654).
Proof. exact (MK_COMB (@lem4891235 _112654) (@lem4891234 _112654)). Qed.
Lemma lem4891238 {_112654 : Type'} (h1 : term7 _112654) : term7 _112654.
Proof. exact (EQ_MP (@lem4891237 _112654) (@lem4891185 _112654 h1)). Qed.
Lemma lem4891240 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term22 _112654 P s) = (term22 _112654 P s).
Proof. exact (eq_refl (term22 _112654 P s)). Qed.
Lemma lem4891241 {_112654 : Type'} (P : type686 _112654) : (term23 _112654 P) = (term23 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891240 _112654 P s)). Qed.
Lemma lem4891242 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891244 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term3 _112654 P).
Proof. exact (MK_COMB (@lem4891242 _112654) (@lem4891241 _112654 P)). Qed.
Lemma lem4891245 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term3 _112654 P.
Proof. exact (EQ_MP (@lem4891244 _112654 P) (@lem4891229 _112654 P s h1)). Qed.
Lemma lem4891262 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4891263 {_112654 : Type'} (P : type686 _112654) : (term21 _112654 P) = (term21 _112654 P).
Proof. exact (fun_ext (fun s : _112654 -> Prop => @lem4891262 _112654 P s)). Qed.
Lemma lem4891264 {_112654 : Type'} : (@all (_112654 -> Prop)) = (@all (_112654 -> Prop)).
Proof. exact (eq_refl (@all (_112654 -> Prop))). Qed.
Lemma lem4891266 {_112654 : Type'} (P : type686 _112654) : (term4 _112654 P) = (term4 _112654 P).
Proof. exact (MK_COMB (@lem4891264 _112654) (@lem4891263 _112654 P)). Qed.
Lemma lem4891267 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term4 _112654 P.
Proof. exact (EQ_MP (@lem4891266 _112654 P) (@lem4891230 _112654 s P h1)). Qed.
Lemma lem4891268 {_112654 : Type'} (_60409 : _112654 -> Prop) (h1 : term7 _112654) : term0 _112654 _60409.
Proof. exact (@lem4891238 _112654 h1 _60409). Qed.
Lemma lem4891269 {_112654 : Type'} (_60409 : _112654 -> Prop) : (term0 _112654 _60409) = ((term1 _112654 _60409) = _60409).
Proof. exact (eq_refl (term0 _112654 _60409)). Qed.
Lemma lem4891271 {_112654 : Type'} (_60410 : _112654 -> Prop) (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term29 _112654 P _60410.
Proof. exact (@lem4891245 _112654 P s h1 _60410). Qed.
Lemma lem4891272 {_112654 : Type'} (P : type686 _112654) (_60410 : _112654 -> Prop) : (term29 _112654 P _60410) = (term22 _112654 P _60410).
Proof. exact (eq_refl (term29 _112654 P _60410)). Qed.
Lemma lem4891277 {_112654 : Type'} (_60412 : _112654 -> Prop) (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term37 _112654 P _60412.
Proof. exact (@lem4891267 _112654 s P h1 _60412). Qed.
Lemma lem4891278 {_112654 : Type'} (P : type686 _112654) (_60412 : _112654 -> Prop) : (term37 _112654 P _60412) = (P _60412).
Proof. exact (eq_refl (term37 _112654 P _60412)). Qed.
Lemma lem4891285 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term39 _112654 P s.
Proof. exact (proj2 (@lem4891226 _112654 P s h1)). Qed.
Lemma lem4891289 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term31 _112654 P s.
Proof. exact (proj1 (@lem4891227 _112654 s P h1)). Qed.
Lemma lem4891292 {_112654 : Type'} (P : type686 _112654) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4891293 {_112654 : Type'} (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) (h1 : _60413 = _60414) : _60413 = _60414.
Proof. exact (h1). Qed.
Lemma lem4891294 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) (h1 : _60413 = _60414) : (P _60413) = (P _60414).
Proof. exact (MK_COMB (@lem4891292 _112654 P) (@lem4891293 _112654 _60413 _60414 h1)). Qed.
Lemma lem4891296 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4891297 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : term113 _112654 _60414 P _60413.
Proof. exact (@lem4891296 (P _60414) (P _60413)). Qed.
Lemma lem4891298 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) (h1 : _60413 = _60414) : term114 _112654 _60414 P _60413.
Proof. exact (@lem4891297 _112654 _60414 P _60413 (@lem4891294 _112654 P _60413 _60414 h1)). Qed.
Lemma lem4891299 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : term115 _112654 _60414 P _60413.
Proof. exact (fun h0 : _60413 = _60414 => @lem4891298 _112654 P _60413 _60414 h0). Qed.
Lemma lem4891301 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4891302 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term115 _112654 _60414 P _60413) = (term117 _112654 _60414 P _60413).
Proof. exact (@lem4891301 (_60413 = _60414) (term114 _112654 _60414 P _60413)). Qed.
Lemma lem4891303 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : term117 _112654 _60414 P _60413.
Proof. exact (EQ_MP (@lem4891302 _112654 _60414 P _60413) (@lem4891299 _112654 _60414 P _60413)). Qed.
Lemma lem4891322 {_112654 : Type'} (_60409 : _112654 -> Prop) (h1 : term7 _112654) : (term1 _112654 _60409) = _60409.
Proof. exact (EQ_MP (@lem4891269 _112654 _60409) (@lem4891268 _112654 _60409 h1)). Qed.
Lemma lem4891323 {_112654 : Type'} (_60409 : _112654 -> Prop) (h1 : term7 _112654) : (term1 _112654 _60409) = _60409.
Proof. exact (@lem4891322 _112654 _60409 h1). Qed.
Lemma lem4891324 {_112654 : Type'} (s : _112654 -> Prop) (h1 : term7 _112654) : (term1 _112654 s) = s.
Proof. exact (@lem4891323 _112654 s h1). Qed.
Lemma lem4891325 {_112654 : Type'} (s : _112654 -> Prop) (h1 : term7 _112654) : term118 _112654 s.
Proof. exact (fun h0 : term119 _112654 s => @lem4891324 _112654 s h1). Qed.
Lemma lem4891327 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891328 {_112654 : Type'} (s : _112654 -> Prop) : (term118 _112654 s) = ((term1 _112654 s) = s).
Proof. exact (@lem4891327 ((term1 _112654 s) = s)). Qed.
Lemma lem4891329 {_112654 : Type'} (s : _112654 -> Prop) (h1 : term7 _112654) : (term1 _112654 s) = s.
Proof. exact (EQ_MP (@lem4891328 _112654 s) (@lem4891325 _112654 s h1)). Qed.
Lemma lem4891331 {_112654 : Type'} (_60410 : _112654 -> Prop) (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term22 _112654 P _60410.
Proof. exact (EQ_MP (@lem4891272 _112654 P _60410) (@lem4891271 _112654 _60410 P s h1)). Qed.
Lemma lem4891332 {_112654 : Type'} (_60410 : _112654 -> Prop) (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term22 _112654 P _60410.
Proof. exact (@lem4891331 _112654 _60410 P s h1). Qed.
Lemma lem4891333 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term121 _112654 P s.
Proof. exact (@lem4891332 _112654 (@DIFF _112654 (@UNIV _112654) s) P s h1). Qed.
Lemma lem4891334 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term122 _112654 P s.
Proof. exact (fun h0 : term123 _112654 P s => @lem4891333 _112654 P s h1). Qed.
Lemma lem4891336 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891337 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term122 _112654 P s) = (term121 _112654 P s).
Proof. exact (@lem4891336 (term121 _112654 P s)). Qed.
Lemma lem4891338 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term121 _112654 P s.
Proof. exact (EQ_MP (@lem4891337 _112654 P s) (@lem4891334 _112654 P s h1)). Qed.
Lemma lem4891344 (q : Prop) (p : Prop) (r : Prop) : (term124 p q r) = (term124 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4891345 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term117 _112654 _60414 P _60413) = (term125 _112654 _60414 P _60413).
Proof. exact (@lem4891344 (P _60414) (term126 _112654 _60413 _60414) (term39 _112654 P _60413)). Qed.
Lemma lem4891359 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4891360 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term127 _112654 _60414 P _60413) = (term128 _112654 P _60413 _60414).
Proof. exact (@lem4891359 (term39 _112654 P _60413) (term126 _112654 _60413 _60414)). Qed.
Lemma lem4891368 {_112654 : Type'} (P : type686 _112654) (_60414 : _112654 -> Prop) : (term129 _112654 P _60414) = (term129 _112654 P _60414).
Proof. exact (eq_refl (term129 _112654 P _60414)). Qed.
Lemma lem4891369 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term125 _112654 _60414 P _60413) = (term130 _112654 P _60413 _60414).
Proof. exact (MK_COMB (@lem4891368 _112654 P _60414) (@lem4891360 _112654 P _60413 _60414)). Qed.
Lemma lem4891380 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term117 _112654 _60414 P _60413) = (term130 _112654 P _60413 _60414).
Proof. exact (TRANS (@lem4891345 _112654 _60414 P _60413) (@lem4891369 _112654 P _60413 _60414)). Qed.
Lemma lem4891381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4891382 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term131 _112654 _60414 P _60413) = (term132 _112654 P _60413 _60414).
Proof. exact (MK_COMB (@lem4891381) (@lem4891380 _112654 P _60413 _60414)). Qed.
Lemma lem4891396 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4891397 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term127 _112654 _60414 P _60413) = (term128 _112654 P _60413 _60414).
Proof. exact (@lem4891396 (term39 _112654 P _60413) (term126 _112654 _60413 _60414)). Qed.
Lemma lem4891405 {_112654 : Type'} (P : type686 _112654) (_60414 : _112654 -> Prop) : (term129 _112654 P _60414) = (term129 _112654 P _60414).
Proof. exact (eq_refl (term129 _112654 P _60414)). Qed.
Lemma lem4891406 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term125 _112654 _60414 P _60413) = (term130 _112654 P _60413 _60414).
Proof. exact (MK_COMB (@lem4891405 _112654 P _60414) (@lem4891397 _112654 P _60413 _60414)). Qed.
Lemma lem4891417 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : ((term117 _112654 _60414 P _60413) = (term125 _112654 _60414 P _60413)) = ((term130 _112654 P _60413 _60414) = (term130 _112654 P _60413 _60414)).
Proof. exact (MK_COMB (@lem4891382 _112654 P _60413 _60414) (@lem4891406 _112654 P _60413 _60414)). Qed.
Lemma lem4891419 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4891420 (x : Prop) : (x = x) = True.
Proof. exact (@lem4891419 Prop x). Qed.
Lemma lem4891421 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : ((term130 _112654 P _60413 _60414) = (term130 _112654 P _60413 _60414)) = True.
Proof. exact (@lem4891420 (term130 _112654 P _60413 _60414)). Qed.
Lemma lem4891422 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : ((term117 _112654 _60414 P _60413) = (term125 _112654 _60414 P _60413)) = True.
Proof. exact (TRANS (@lem4891417 _112654 P _60413 _60414) (@lem4891421 _112654 P _60413 _60414)). Qed.
Lemma lem4891423 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : True = ((term117 _112654 _60414 P _60413) = (term125 _112654 _60414 P _60413)).
Proof. exact (SYM (@lem4891422 _112654 _60414 P _60413)). Qed.
Lemma lem4891424 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term117 _112654 _60414 P _60413) = (term125 _112654 _60414 P _60413).
Proof. exact (EQ_MP (@lem4891423 _112654 _60414 P _60413) (@lem0)). Qed.
Lemma lem4891425 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : term125 _112654 _60414 P _60413.
Proof. exact (EQ_MP (@lem4891424 _112654 _60414 P _60413) (@lem4891303 _112654 _60414 P _60413)). Qed.
Lemma lem4891427 (b : Prop) (a : Prop) : (a \/ b) = (term133 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4891428 {_112654 : Type'} (_60413 : _112654 -> Prop) (P : type686 _112654) (_60414 : _112654 -> Prop) : (term125 _112654 _60414 P _60413) = (term134 _112654 _60413 P _60414).
Proof. exact (@lem4891427 (term127 _112654 _60414 P _60413) (P _60414)). Qed.
Lemma lem4891430 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4891431 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term137 _112654 _60414 P _60413) = (term138 _112654 _60414 P _60413).
Proof. exact (@lem4891430 (term126 _112654 _60413 _60414) (term39 _112654 P _60413)). Qed.
Lemma lem4891433 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4891434 {_112654 : Type'} (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term140 _112654 _60413 _60414) = (_60413 = _60414).
Proof. exact (@lem4891433 (_60413 = _60414)). Qed.
Lemma lem4891435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891436 {_112654 : Type'} (_60413 : _112654 -> Prop) (_60414 : _112654 -> Prop) : (term141 _112654 _60413 _60414) = (term142 _112654 _60413 _60414).
Proof. exact (MK_COMB (@lem4891435) (@lem4891434 _112654 _60413 _60414)). Qed.
Lemma lem4891438 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4891439 {_112654 : Type'} (P : type686 _112654) (_60413 : _112654 -> Prop) : (term143 _112654 P _60413) = (P _60413).
Proof. exact (@lem4891438 (P _60413)). Qed.
Lemma lem4891440 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term138 _112654 _60414 P _60413) = (term144 _112654 _60414 P _60413).
Proof. exact (MK_COMB (@lem4891436 _112654 _60413 _60414) (@lem4891439 _112654 P _60413)). Qed.
Lemma lem4891441 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term137 _112654 _60414 P _60413) = (term144 _112654 _60414 P _60413).
Proof. exact (TRANS (@lem4891431 _112654 _60414 P _60413) (@lem4891440 _112654 _60414 P _60413)). Qed.
Lemma lem4891442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4891443 {_112654 : Type'} (_60414 : _112654 -> Prop) (P : type686 _112654) (_60413 : _112654 -> Prop) : (term145 _112654 _60414 P _60413) = (term146 _112654 _60414 P _60413).
Proof. exact (MK_COMB (@lem4891442) (@lem4891441 _112654 _60414 P _60413)). Qed.
Lemma lem4891444 {_112654 : Type'} (P : type686 _112654) (_60414 : _112654 -> Prop) : (P _60414) = (P _60414).
Proof. exact (eq_refl (P _60414)). Qed.
Lemma lem4891445 {_112654 : Type'} (_60413 : _112654 -> Prop) (P : type686 _112654) (_60414 : _112654 -> Prop) : (term134 _112654 _60413 P _60414) = (term147 _112654 _60413 P _60414).
Proof. exact (MK_COMB (@lem4891443 _112654 _60414 P _60413) (@lem4891444 _112654 P _60414)). Qed.
Lemma lem4891446 {_112654 : Type'} (_60413 : _112654 -> Prop) (P : type686 _112654) (_60414 : _112654 -> Prop) : (term125 _112654 _60414 P _60413) = (term147 _112654 _60413 P _60414).
Proof. exact (TRANS (@lem4891428 _112654 _60413 P _60414) (@lem4891445 _112654 _60413 P _60414)). Qed.
Lemma lem4891448 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : term148 _112654 P s.
Proof. exact (conj (@lem4891329 _112654 s h1) (@lem4891338 _112654 P s h2)). Qed.
Lemma lem4891450 {_112654 : Type'} (_60413 : _112654 -> Prop) (P : type686 _112654) (_60414 : _112654 -> Prop) : term147 _112654 _60413 P _60414.
Proof. exact (EQ_MP (@lem4891446 _112654 _60413 P _60414) (@lem4891425 _112654 _60414 P _60413)). Qed.
Lemma lem4891451 {_112654 : Type'} (_60413 : _112654 -> Prop) (P : type686 _112654) (_60414 : _112654 -> Prop) : term147 _112654 _60413 P _60414.
Proof. exact (@lem4891450 _112654 _60413 P _60414). Qed.
Lemma lem4891452 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : term149 _112654 P s.
Proof. exact (@lem4891451 _112654 (term1 _112654 s) P s). Qed.
Lemma lem4891455 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : P s.
Proof. exact (@lem4891452 _112654 P s (@lem4891448 _112654 P s h1 h2)). Qed.
Lemma lem4891456 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : term150 _112654 P s.
Proof. exact (fun h0 : term39 _112654 P s => @lem4891455 _112654 P s h1 h2). Qed.
Lemma lem4891458 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891459 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term150 _112654 P s) = (P s).
Proof. exact (@lem4891458 (P s)). Qed.
Lemma lem4891460 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : P s.
Proof. exact (EQ_MP (@lem4891459 _112654 P s) (@lem4891456 _112654 P s h1 h2)). Qed.
Lemma lem4891463 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4891465 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term39 _112654 P s) = (term151 _112654 P s).
Proof. exact (@lem4891463 (P s)). Qed.
Lemma lem4891468 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term65 _112654 P s) : term151 _112654 P s.
Proof. exact (EQ_MP (@lem4891465 _112654 P s) (@lem4891285 _112654 P s h1)). Qed.
Lemma lem4891471 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : False.
Proof. exact (@lem4891468 _112654 P s h2 (@lem4891460 _112654 P s h1 h2)). Qed.
Lemma lem4891472 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : term152.
Proof. exact (fun h0 : ~ False => @lem4891471 _112654 P s h1 h2). Qed.
Lemma lem4891474 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891475 : term152 = False.
Proof. exact (@lem4891474 False). Qed.
Lemma lem4891476 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : False.
Proof. exact (EQ_MP (@lem4891475) (@lem4891472 _112654 P s h1 h2)). Qed.
Lemma lem4891507 {_112654 : Type'} (_60412 : _112654 -> Prop) (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : P _60412.
Proof. exact (EQ_MP (@lem4891278 _112654 P _60412) (@lem4891277 _112654 _60412 s P h1)). Qed.
Lemma lem4891508 {_112654 : Type'} (_60412 : _112654 -> Prop) (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : P _60412.
Proof. exact (@lem4891507 _112654 _60412 s P h1). Qed.
Lemma lem4891509 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term22 _112654 P s.
Proof. exact (@lem4891508 _112654 (@DIFF _112654 (@UNIV _112654) s) s P h1). Qed.
Lemma lem4891510 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term153 _112654 P s.
Proof. exact (fun h0 : term31 _112654 P s => @lem4891509 _112654 s P h1). Qed.
Lemma lem4891512 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891513 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term153 _112654 P s) = (term22 _112654 P s).
Proof. exact (@lem4891512 (term22 _112654 P s)). Qed.
Lemma lem4891514 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term22 _112654 P s.
Proof. exact (EQ_MP (@lem4891513 _112654 P s) (@lem4891510 _112654 s P h1)). Qed.
Lemma lem4891517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4891519 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) : (term31 _112654 P s) = (term154 _112654 P s).
Proof. exact (@lem4891517 (term22 _112654 P s)). Qed.
Lemma lem4891522 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term154 _112654 P s.
Proof. exact (EQ_MP (@lem4891519 _112654 P s) (@lem4891289 _112654 s P h1)). Qed.
Lemma lem4891525 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : False.
Proof. exact (@lem4891522 _112654 s P h1 (@lem4891514 _112654 s P h1)). Qed.
Lemma lem4891526 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : term152.
Proof. exact (fun h0 : ~ False => @lem4891525 _112654 s P h1). Qed.
Lemma lem4891528 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4891529 : term152 = False.
Proof. exact (@lem4891528 False). Qed.
Lemma lem4891530 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term85 _112654 s P) : False.
Proof. exact (EQ_MP (@lem4891529) (@lem4891526 _112654 s P h1)). Qed.
Lemma lem4891531 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : (term7 _112654) = False.
Proof. exact (prop_ext (fun h3 : term7 _112654 => @lem4891476 _112654 P s h1 h2) (fun h3 : False => @lem4891238 _112654 h1)). Qed.
Lemma lem4891532 {_112654 : Type'} (P : type686 _112654) (s : _112654 -> Prop) (h1 : term7 _112654) (h2 : term65 _112654 P s) : False.
Proof. exact (EQ_MP (@lem4891531 _112654 P s h1 h2) (@lem4891238 _112654 h1)). Qed.
Lemma lem4891533 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term7 _112654) (h2 : term108 _112654 s P) : False.
Proof. exact (or_elim (@lem4891225 _112654 s P h2) (fun h0 : term65 _112654 P s => @lem4891532 _112654 P s h1 h0) (fun h0 : term85 _112654 s P => @lem4891530 _112654 s P h0)). Qed.
Lemma lem4891534 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term7 _112654) (h2 : term108 _112654 s P) : (term108 _112654 s P) = False.
Proof. exact (prop_ext (fun h3 : term108 _112654 s P => @lem4891533 _112654 s P h1 h2) (fun h3 : False => @lem4891225 _112654 s P h2)). Qed.
Lemma lem4891535 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term7 _112654) (h2 : term108 _112654 s P) : False.
Proof. exact (EQ_MP (@lem4891534 _112654 s P h1 h2) (@lem4891225 _112654 s P h2)). Qed.
Lemma lem4891536 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term7 _112654) (h2 : term108 _112654 s P) : (term7 _112654) = False.
Proof. exact (prop_ext (fun h3 : term7 _112654 => @lem4891535 _112654 s P h1 h2) (fun h3 : False => @lem4891185 _112654 h1)). Qed.
Lemma lem4891537 {_112654 : Type'} (s : _112654 -> Prop) (P : type686 _112654) (h1 : term7 _112654) (h2 : term108 _112654 s P) : False.
Proof. exact (EQ_MP (@lem4891536 _112654 s P h1 h2) (@lem4891185 _112654 h1)). Qed.
Lemma lem4891538 {_112654 : Type'} (P : type686 _112654) (h1 : term7 _112654) (h2 : term6 _112654 P) : False.
Proof. exact (ex_elim (@lem4891154 _112654 P h2) (fun s : _112654 -> Prop => fun h0 : term110 _112654 P s => @lem4891537 _112654 s P h1 h0)). Qed.
Lemma lem4891539 {_112654 : Type'} (P : type686 _112654) (h1 : term7 _112654) (h2 : term6 _112654 P) : (term7 _112654) = False.
Proof. exact (prop_ext (fun h3 : term7 _112654 => @lem4891538 _112654 P h1 h2) (fun h3 : False => @lem4891167 _112654 h1)). Qed.
Lemma lem4891540 {_112654 : Type'} (P : type686 _112654) (h1 : term7 _112654) (h2 : term6 _112654 P) : False.
Proof. exact (EQ_MP (@lem4891539 _112654 P h1 h2) (@lem4891167 _112654 h1)). Qed.
Lemma lem4891541 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term12 _112654.
Proof. exact (fun h0 : term7 _112654 => @lem4891540 _112654 P h0 h1). Qed.
Lemma lem4891542 {_112654 : Type'} : (term12 _112654) = (term13 _112654).
Proof. exact (@lem69 (term7 _112654)). Qed.
Lemma lem4891543 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term13 _112654.
Proof. exact (EQ_MP (@lem4891542 _112654) (@lem4891541 _112654 P h1)). Qed.
Lemma lem4891544 {_112654 : Type'} (P : type686 _112654) : term15 _112654 P.
Proof. exact (fun h0 : term6 _112654 P => @lem4891543 _112654 P h0). Qed.
Lemma lem4891549 {_112654 : Type'} : term19 _112654.
Proof. exact (fun P : type686 _112654 => @lem4891544 _112654 P). Qed.
Lemma lem4891550 {_112654 : Type'} : term18 _112654.
Proof. exact (EQ_MP (@lem4891016 _112654) (@lem4891549 _112654)). Qed.
Lemma lem4891551 {_112654 : Type'} (P : type686 _112654) : term155 _112654 P.
Proof. exact (@lem4891550 _112654 P). Qed.
Lemma lem4891552 {_112654 : Type'} (P : type686 _112654) : (term155 _112654 P) = (term8 _112654 P).
Proof. exact (eq_refl (term155 _112654 P)). Qed.
Lemma lem4891553 {_112654 : Type'} (P : type686 _112654) : term8 _112654 P.
Proof. exact (EQ_MP (@lem4891552 _112654 P) (@lem4891551 _112654 P)). Qed.
Lemma lem4891555 {_112654 : Type'} (P : type686 _112654) : term8 _112654 P.
Proof. exact (@lem4890925 _112654 P (@lem4891553 _112654 P)). Qed.
Lemma lem4891556 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : term12 _112654.
Proof. exact (@lem4891555 _112654 P (@lem4890907 _112654 P h1)). Qed.
Lemma lem4891557 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : False.
Proof. exact (@lem4891556 _112654 P h1 (@lem4890908 _112654)). Qed.
Lemma lem4891558 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : (term6 _112654 P) = False.
Proof. exact (prop_ext (fun h2 : term6 _112654 P => @lem4891557 _112654 P h1) (fun h2 : False => @lem4890907 _112654 P h1)). Qed.
Lemma lem4891559 {_112654 : Type'} (P : type686 _112654) (h1 : term6 _112654 P) : False.
Proof. exact (EQ_MP (@lem4891558 _112654 P h1) (@lem4890907 _112654 P h1)). Qed.
Lemma lem4891560 {_112654 : Type'} (P : type686 _112654) : term5 _112654 P.
Proof. exact (fun h0 : term6 _112654 P => @lem4891559 _112654 P h0). Qed.
Lemma lem4891575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term156 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4891576 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (s = t) = (term156 _112681 s t).
Proof. exact (@lem4891575 _112681 s t). Qed.
Lemma lem4891577 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : ((@INTER _112681 s t) = (term157 _112681 s t)) = (term158 _112681 s t).
Proof. exact (@lem4891576 _112681 (@INTER _112681 s t) (term157 _112681 s t)). Qed.
Lemma lem4891586 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term158 _112681 s t) = ((@INTER _112681 s t) = (term157 _112681 s t)).
Proof. exact (SYM (@lem4891577 _112681 s t)). Qed.
Lemma lem4891594 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term159 A x s t) = (term160 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4891595 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term159 _112681 x s t) = (term160 _112681 s x t).
Proof. exact (@lem4891594 _112681 s x t). Qed.
Lemma lem4891599 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4891600 {_112681 : Type'} (P : _112681 -> Prop) (x : _112681) : (@IN _112681 x P) = (P x).
Proof. exact (@lem4891599 _112681 P x). Qed.
Lemma lem4891601 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (@IN _112681 x s) = (s x).
Proof. exact (@lem4891600 _112681 s x). Qed.
Lemma lem4891602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891603 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term161 _112681 x s) = (term162 _112681 s x).
Proof. exact (MK_COMB (@lem4891602) (@lem4891601 _112681 s x)). Qed.
Lemma lem4891605 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4891606 {_112681 : Type'} (P : _112681 -> Prop) (x : _112681) : (@IN _112681 x P) = (P x).
Proof. exact (@lem4891605 _112681 P x). Qed.
Lemma lem4891607 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (@IN _112681 x t) = (t x).
Proof. exact (@lem4891606 _112681 t x). Qed.
Lemma lem4891608 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term160 _112681 s x t) = (term163 _112681 s t x).
Proof. exact (MK_COMB (@lem4891603 _112681 s x) (@lem4891607 _112681 t x)). Qed.
Lemma lem4891611 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term159 _112681 x s t) = (term163 _112681 s t x).
Proof. exact (TRANS (@lem4891595 _112681 s x t) (@lem4891608 _112681 s t x)). Qed.
Lemma lem4891612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4891613 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term164 _112681 x s t) = (term165 _112681 s t x).
Proof. exact (MK_COMB (@lem4891612) (@lem4891611 _112681 s t x)). Qed.
Lemma lem4891615 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4891616 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term166 _112681 x s t) = (term167 _112681 s x t).
Proof. exact (@lem4891615 _112681 s x t). Qed.
Lemma lem4891617 {_112681 : Type'} (x : _112681) (s : _112681 -> Prop) (t : _112681 -> Prop) : (term168 _112681 x s t) = (term169 _112681 x s t).
Proof. exact (@lem4891616 _112681 (@UNIV _112681) x (term170 _112681 s t)). Qed.
Lemma lem4891621 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4891622 {_112681 : Type'} (x : _112681) : (@IN _112681 x (@UNIV _112681)) = True.
Proof. exact (@lem4891621 _112681 x). Qed.
Lemma lem4891623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891624 {_112681 : Type'} (x : _112681) : (term171 _112681 x) = (and True).
Proof. exact (MK_COMB (@lem4891623) (@lem4891622 _112681 x)). Qed.
Lemma lem4891626 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term172 A x s t) = (term173 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4891627 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term172 _112681 x s t) = (term173 _112681 s x t).
Proof. exact (@lem4891626 _112681 s x t). Qed.
Lemma lem4891628 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term174 _112681 x s t) = (term175 _112681 s x t).
Proof. exact (@lem4891627 _112681 (@DIFF _112681 (@UNIV _112681) s) x (@DIFF _112681 (@UNIV _112681) t)). Qed.
Lemma lem4891632 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4891633 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term166 _112681 x s t) = (term167 _112681 s x t).
Proof. exact (@lem4891632 _112681 s x t). Qed.
Lemma lem4891634 {_112681 : Type'} (x : _112681) (s : _112681 -> Prop) : (term176 _112681 x s) = (term177 _112681 x s).
Proof. exact (@lem4891633 _112681 (@UNIV _112681) x s). Qed.
Lemma lem4891638 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4891639 {_112681 : Type'} (x : _112681) : (@IN _112681 x (@UNIV _112681)) = True.
Proof. exact (@lem4891638 _112681 x). Qed.
Lemma lem4891640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891641 {_112681 : Type'} (x : _112681) : (term171 _112681 x) = (and True).
Proof. exact (MK_COMB (@lem4891640) (@lem4891639 _112681 x)). Qed.
Lemma lem4891643 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4891644 {_112681 : Type'} (P : _112681 -> Prop) (x : _112681) : (@IN _112681 x P) = (P x).
Proof. exact (@lem4891643 _112681 P x). Qed.
Lemma lem4891645 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (@IN _112681 x s) = (s x).
Proof. exact (@lem4891644 _112681 s x). Qed.
Lemma lem4891646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4891647 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term178 _112681 x s) = (term179 _112681 s x).
Proof. exact (MK_COMB (@lem4891646) (@lem4891645 _112681 s x)). Qed.
Lemma lem4891648 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term177 _112681 x s) = (term180 _112681 s x).
Proof. exact (MK_COMB (@lem4891641 _112681 x) (@lem4891647 _112681 s x)). Qed.
Lemma lem4891650 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4891651 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term180 _112681 s x) = (term179 _112681 s x).
Proof. exact (@lem4891650 (term179 _112681 s x)). Qed.
Lemma lem4891652 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term177 _112681 x s) = (term179 _112681 s x).
Proof. exact (TRANS (@lem4891648 _112681 s x) (@lem4891651 _112681 s x)). Qed.
Lemma lem4891653 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term176 _112681 x s) = (term179 _112681 s x).
Proof. exact (TRANS (@lem4891634 _112681 x s) (@lem4891652 _112681 s x)). Qed.
Lemma lem4891654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891655 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term181 _112681 x s) = (term182 _112681 s x).
Proof. exact (MK_COMB (@lem4891654) (@lem4891653 _112681 s x)). Qed.
Lemma lem4891657 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4891658 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (t : _112681 -> Prop) : (term166 _112681 x s t) = (term167 _112681 s x t).
Proof. exact (@lem4891657 _112681 s x t). Qed.
Lemma lem4891659 {_112681 : Type'} (x : _112681) (t : _112681 -> Prop) : (term176 _112681 x t) = (term177 _112681 x t).
Proof. exact (@lem4891658 _112681 (@UNIV _112681) x t). Qed.
Lemma lem4891663 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4891664 {_112681 : Type'} (x : _112681) : (@IN _112681 x (@UNIV _112681)) = True.
Proof. exact (@lem4891663 _112681 x). Qed.
Lemma lem4891665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891666 {_112681 : Type'} (x : _112681) : (term171 _112681 x) = (and True).
Proof. exact (MK_COMB (@lem4891665) (@lem4891664 _112681 x)). Qed.
Lemma lem4891668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4891669 {_112681 : Type'} (P : _112681 -> Prop) (x : _112681) : (@IN _112681 x P) = (P x).
Proof. exact (@lem4891668 _112681 P x). Qed.
Lemma lem4891670 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (@IN _112681 x t) = (t x).
Proof. exact (@lem4891669 _112681 t x). Qed.
Lemma lem4891671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4891672 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term178 _112681 x t) = (term179 _112681 t x).
Proof. exact (MK_COMB (@lem4891671) (@lem4891670 _112681 t x)). Qed.
Lemma lem4891673 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term177 _112681 x t) = (term180 _112681 t x).
Proof. exact (MK_COMB (@lem4891666 _112681 x) (@lem4891672 _112681 t x)). Qed.
Lemma lem4891675 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4891676 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term180 _112681 t x) = (term179 _112681 t x).
Proof. exact (@lem4891675 (term179 _112681 t x)). Qed.
Lemma lem4891677 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term177 _112681 x t) = (term179 _112681 t x).
Proof. exact (TRANS (@lem4891673 _112681 t x) (@lem4891676 _112681 t x)). Qed.
Lemma lem4891678 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term176 _112681 x t) = (term179 _112681 t x).
Proof. exact (TRANS (@lem4891659 _112681 x t) (@lem4891677 _112681 t x)). Qed.
Lemma lem4891679 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term175 _112681 s x t) = (term183 _112681 s t x).
Proof. exact (MK_COMB (@lem4891655 _112681 s x) (@lem4891678 _112681 t x)). Qed.
Lemma lem4891682 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term174 _112681 x s t) = (term183 _112681 s t x).
Proof. exact (TRANS (@lem4891628 _112681 s x t) (@lem4891679 _112681 s t x)). Qed.
Lemma lem4891683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4891684 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term184 _112681 x s t) = (term185 _112681 s t x).
Proof. exact (MK_COMB (@lem4891683) (@lem4891682 _112681 s t x)). Qed.
Lemma lem4891685 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term169 _112681 x s t) = (term186 _112681 s t x).
Proof. exact (MK_COMB (@lem4891624 _112681 x) (@lem4891684 _112681 s t x)). Qed.
Lemma lem4891687 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4891688 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term186 _112681 s t x) = (term185 _112681 s t x).
Proof. exact (@lem4891687 (term185 _112681 s t x)). Qed.
Lemma lem4891691 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term169 _112681 x s t) = (term185 _112681 s t x).
Proof. exact (TRANS (@lem4891685 _112681 s t x) (@lem4891688 _112681 s t x)). Qed.
Lemma lem4891692 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term168 _112681 x s t) = (term185 _112681 s t x).
Proof. exact (TRANS (@lem4891617 _112681 x s t) (@lem4891691 _112681 s t x)). Qed.
Lemma lem4891693 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : ((term159 _112681 x s t) = (term168 _112681 x s t)) = ((term163 _112681 s t x) = (term185 _112681 s t x)).
Proof. exact (MK_COMB (@lem4891613 _112681 s t x) (@lem4891692 _112681 s t x)). Qed.
Lemma lem4891696 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term187 _112681 s t) = (term188 _112681 s t).
Proof. exact (fun_ext (fun x : _112681 => @lem4891693 _112681 s t x)). Qed.
Lemma lem4891697 {_112681 : Type'} : (@all _112681) = (@all _112681).
Proof. exact (eq_refl (@all _112681)). Qed.
Lemma lem4891698 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term158 _112681 s t) = (term189 _112681 s t).
Proof. exact (MK_COMB (@lem4891697 _112681) (@lem4891696 _112681 s t)). Qed.
Lemma lem4891703 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term189 _112681 s t) = (term158 _112681 s t).
Proof. exact (SYM (@lem4891698 _112681 s t)). Qed.
Lemma lem4891705 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4891706 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term189 _112681 s t) = (term190 _112681 s t).
Proof. exact (@lem4891705 (term189 _112681 s t)). Qed.
Lemma lem4891707 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term190 _112681 s t) = (term189 _112681 s t).
Proof. exact (SYM (@lem4891706 _112681 s t)). Qed.
Lemma lem4891708 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term191 _112681 s t) : term191 _112681 s t.
Proof. exact (h1). Qed.
Lemma lem4891711 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term190 _112681 s t) : term190 _112681 s t.
Proof. exact (h1). Qed.
Lemma lem4891712 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term192 _112681 s t.
Proof. exact (fun h0 : term190 _112681 s t => @lem4891711 _112681 s t h0). Qed.
Lemma lem4891713 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term192 _112681 s t) : term192 _112681 s t.
Proof. exact (h1). Qed.
Lemma lem4891714 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term190 _112681 s t) : term190 _112681 s t.
Proof. exact (h1). Qed.
Lemma lem4891715 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term190 _112681 s t) (h2 : term192 _112681 s t) : term190 _112681 s t.
Proof. exact (@lem4891713 _112681 s t h2 (@lem4891714 _112681 s t h1)). Qed.
Lemma lem4891716 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term190 _112681 s t) : term193 _112681 s t.
Proof. exact (fun h0 : term192 _112681 s t => @lem4891715 _112681 s t h1 h0). Qed.
Lemma lem4891717 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term192 _112681 s t) : term192 _112681 s t.
Proof. exact (h1). Qed.
Lemma lem4891718 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term190 _112681 s t) (h2 : term192 _112681 s t) : term190 _112681 s t.
Proof. exact (@lem4891716 _112681 s t h1 (@lem4891717 _112681 s t h2)). Qed.
Lemma lem4891719 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term192 _112681 s t) : term192 _112681 s t.
Proof. exact (fun h0 : term190 _112681 s t => @lem4891718 _112681 s t h0 h1). Qed.
Lemma lem4891720 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term194 _112681 s t.
Proof. exact (fun h0 : term192 _112681 s t => @lem4891719 _112681 s t h0). Qed.
Lemma lem4891723 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term192 _112681 s t.
Proof. exact (@lem4891720 _112681 s t (@lem4891712 _112681 s t)). Qed.
Lemma lem4891724 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term192 _112681 s t.
Proof. exact (@lem4891723 _112681 s t). Qed.
Lemma lem4891734 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4891735 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term190 _112681 s t) = (term195 _112681 s t).
Proof. exact (@lem4891734 (term191 _112681 s t)). Qed.
Lemma lem4891737 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4891738 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term195 _112681 s t) = (term189 _112681 s t).
Proof. exact (@lem4891737 (term189 _112681 s t)). Qed.
Lemma lem4891743 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term190 _112681 s t) = (term189 _112681 s t).
Proof. exact (TRANS (@lem4891735 _112681 s t) (@lem4891738 _112681 s t)). Qed.
Lemma lem4891748 {_112681 : Type'} (t : _112681 -> Prop) : (term196 _112681 t) = (term197 _112681 t).
Proof. exact (fun_ext (fun s : _112681 -> Prop => @lem4891743 _112681 s t)). Qed.
Lemma lem4891749 {_112681 : Type'} : (@all (_112681 -> Prop)) = (@all (_112681 -> Prop)).
Proof. exact (eq_refl (@all (_112681 -> Prop))). Qed.
Lemma lem4891750 {_112681 : Type'} (t : _112681 -> Prop) : (term198 _112681 t) = (term199 _112681 t).
Proof. exact (MK_COMB (@lem4891749 _112681) (@lem4891748 _112681 t)). Qed.
Lemma lem4891755 {_112681 : Type'} : (term200 _112681) = (term201 _112681).
Proof. exact (fun_ext (fun t : _112681 -> Prop => @lem4891750 _112681 t)). Qed.
Lemma lem4891756 {_112681 : Type'} : (@all (_112681 -> Prop)) = (@all (_112681 -> Prop)).
Proof. exact (eq_refl (@all (_112681 -> Prop))). Qed.
Lemma lem4891765 {_112681 : Type'} : (term202 _112681) = (term203 _112681).
Proof. exact (MK_COMB (@lem4891756 _112681) (@lem4891755 _112681)). Qed.
Lemma lem4891784 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : ((term163 _112681 s t x) = (term185 _112681 s t x)) = ((term163 _112681 s t x) = (term185 _112681 s t x)).
Proof. exact (eq_refl ((term163 _112681 s t x) = (term185 _112681 s t x))). Qed.
Lemma lem4891785 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term188 _112681 s t) = (term188 _112681 s t).
Proof. exact (fun_ext (fun x : _112681 => @lem4891784 _112681 s t x)). Qed.
Lemma lem4891786 {_112681 : Type'} : (@all _112681) = (@all _112681).
Proof. exact (eq_refl (@all _112681)). Qed.
Lemma lem4891787 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term189 _112681 s t) = (term189 _112681 s t).
Proof. exact (MK_COMB (@lem4891786 _112681) (@lem4891785 _112681 s t)). Qed.
Lemma lem4891788 {_112681 : Type'} (t : _112681 -> Prop) : (term197 _112681 t) = (term197 _112681 t).
Proof. exact (fun_ext (fun s : _112681 -> Prop => @lem4891787 _112681 s t)). Qed.
Lemma lem4891789 {_112681 : Type'} : (@all (_112681 -> Prop)) = (@all (_112681 -> Prop)).
Proof. exact (eq_refl (@all (_112681 -> Prop))). Qed.
Lemma lem4891790 {_112681 : Type'} (t : _112681 -> Prop) : (term199 _112681 t) = (term199 _112681 t).
Proof. exact (MK_COMB (@lem4891789 _112681) (@lem4891788 _112681 t)). Qed.
Lemma lem4891791 {_112681 : Type'} : (term201 _112681) = (term201 _112681).
Proof. exact (fun_ext (fun t : _112681 -> Prop => @lem4891790 _112681 t)). Qed.
Lemma lem4891792 {_112681 : Type'} : (@all (_112681 -> Prop)) = (@all (_112681 -> Prop)).
Proof. exact (eq_refl (@all (_112681 -> Prop))). Qed.
Lemma lem4891793 {_112681 : Type'} : (term203 _112681) = (term203 _112681).
Proof. exact (MK_COMB (@lem4891792 _112681) (@lem4891791 _112681)). Qed.
Lemma lem4891818 {_112681 : Type'} : (term202 _112681) = (term203 _112681).
Proof. exact (TRANS (@lem4891765 _112681) (@lem4891793 _112681)). Qed.
Lemma lem4891819 {_112681 : Type'} : (term203 _112681) = (term202 _112681).
Proof. exact (SYM (@lem4891818 _112681)). Qed.
Lemma lem4891821 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4891822 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : ((term163 _112681 s t x) = (term185 _112681 s t x)) = (term204 _112681 s t x).
Proof. exact (@lem4891821 ((term163 _112681 s t x) = (term185 _112681 s t x))). Qed.
Lemma lem4891823 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term204 _112681 s t x) = ((term163 _112681 s t x) = (term185 _112681 s t x)).
Proof. exact (SYM (@lem4891822 _112681 s t x)). Qed.
Lemma lem4891824 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term205 _112681 s t x) : term205 _112681 s t x.
Proof. exact (h1). Qed.
Lemma lem4891833 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term206 _112681 s t x) = (term183 _112681 s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem4891840 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term207 _112681 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4891844 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term207 _112681 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4891845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891846 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term208 _112681 s x) = (term162 _112681 s x).
Proof. exact (MK_COMB (@lem4891845) (@lem4891840 _112681 s x)). Qed.
Lemma lem4891847 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term209 _112681 s t x) = (term163 _112681 s t x).
Proof. exact (MK_COMB (@lem4891846 _112681 s x) (@lem4891844 _112681 t x)). Qed.
Lemma lem4891848 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term185 _112681 s t x) = (term209 _112681 s t x).
Proof. exact (@lem17160 (term179 _112681 s x) (term179 _112681 t x)). Qed.
Lemma lem4891849 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term185 _112681 s t x) = (term163 _112681 s t x).
Proof. exact (TRANS (@lem4891848 _112681 s t x) (@lem4891847 _112681 s t x)). Qed.
Lemma lem4891854 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term210 _112681 s t x) = (term183 _112681 s t x).
Proof. exact (@lem16933 (term183 _112681 s t x)). Qed.
Lemma lem4891855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4891856 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term211 _112681 s t x) = (term212 _112681 s t x).
Proof. exact (MK_COMB (@lem4891855) (@lem4891833 _112681 s t x)). Qed.
Lemma lem4891857 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term213 _112681 s t x) = (term214 _112681 s t x).
Proof. exact (MK_COMB (@lem4891856 _112681 s t x) (@lem4891849 _112681 s t x)). Qed.
Lemma lem4891859 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term215 _112681 s t x) = (term215 _112681 s t x).
Proof. exact (eq_refl (term215 _112681 s t x)). Qed.
Lemma lem4891860 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term216 _112681 s t x) = (term217 _112681 s t x).
Proof. exact (MK_COMB (@lem4891859 _112681 s t x) (@lem4891854 _112681 s t x)). Qed.
Lemma lem4891861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4891862 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term218 _112681 s t x) = (term219 _112681 s t x).
Proof. exact (MK_COMB (@lem4891861) (@lem4891860 _112681 s t x)). Qed.
Lemma lem4891863 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term220 _112681 s t x) = (term221 _112681 s t x).
Proof. exact (MK_COMB (@lem4891862 _112681 s t x) (@lem4891857 _112681 s t x)). Qed.
Lemma lem4891864 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term205 _112681 s t x) = (term220 _112681 s t x).
Proof. exact (@lem17646 (term163 _112681 s t x) (term185 _112681 s t x)). Qed.
Lemma lem4891869 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term205 _112681 s t x) = (term221 _112681 s t x).
Proof. exact (TRANS (@lem4891864 _112681 s t x) (@lem4891863 _112681 s t x)). Qed.
Lemma lem4891924 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term205 _112681 s t x) : term221 _112681 s t x.
Proof. exact (EQ_MP (@lem4891869 _112681 s t x) (@lem4891824 _112681 s t x h1)). Qed.
Lemma lem4891925 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : term217 _112681 s t x.
Proof. exact (h1). Qed.
Lemma lem4891926 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : term214 _112681 s t x.
Proof. exact (h1). Qed.
Lemma lem4891927 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : term183 _112681 s t x.
Proof. exact (proj2 (@lem4891925 _112681 s t x h1)). Qed.
Lemma lem4891928 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : term163 _112681 s t x.
Proof. exact (proj1 (@lem4891925 _112681 s t x h1)). Qed.
Lemma lem4891933 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : term163 _112681 s t x.
Proof. exact (proj2 (@lem4891926 _112681 s t x h1)). Qed.
Lemma lem4891934 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : term183 _112681 s t x.
Proof. exact (proj1 (@lem4891926 _112681 s t x h1)). Qed.
Lemma lem4891950 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term179 _112681 s x.
Proof. exact (h1). Qed.
Lemma lem4891962 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term179 _112681 t x.
Proof. exact (h1). Qed.
Lemma lem4891974 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term179 _112681 s x.
Proof. exact (h1). Qed.
Lemma lem4891986 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term179 _112681 t x.
Proof. exact (h1). Qed.
Lemma lem4891992 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term179 _112681 s x.
Proof. exact (h1). Qed.
Lemma lem4891998 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term179 _112681 t x.
Proof. exact (h1). Qed.
Lemma lem4892004 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term179 _112681 s x.
Proof. exact (h1). Qed.
Lemma lem4892010 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term179 _112681 t x.
Proof. exact (h1). Qed.
Lemma lem4892012 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : s x.
Proof. exact (proj1 (@lem4891928 _112681 s t x h1)). Qed.
Lemma lem4892013 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : term222 _112681 s x.
Proof. exact (fun h0 : term179 _112681 s x => @lem4892012 _112681 s t x h1). Qed.
Lemma lem4892015 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892016 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term222 _112681 s x) = (s x).
Proof. exact (@lem4892015 (s x)). Qed.
Lemma lem4892017 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : s x.
Proof. exact (EQ_MP (@lem4892016 _112681 s x) (@lem4892013 _112681 s t x h1)). Qed.
Lemma lem4892020 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892022 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term179 _112681 s x) = (term223 _112681 s x).
Proof. exact (@lem4892020 (s x)). Qed.
Lemma lem4892025 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term223 _112681 s x.
Proof. exact (EQ_MP (@lem4892022 _112681 s x) (@lem4891992 _112681 s x h1)). Qed.
Lemma lem4892028 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : False.
Proof. exact (@lem4892025 _112681 s x h1 (@lem4892017 _112681 s t x h2)). Qed.
Lemma lem4892029 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4892028 _112681 s t x h1 h2). Qed.
Lemma lem4892031 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892032 : term152 = False.
Proof. exact (@lem4892031 False). Qed.
Lemma lem4892033 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892032) (@lem4892029 _112681 s t x h1 h2)). Qed.
Lemma lem4892035 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : t x.
Proof. exact (proj2 (@lem4891928 _112681 s t x h1)). Qed.
Lemma lem4892036 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : term222 _112681 t x.
Proof. exact (fun h0 : term179 _112681 t x => @lem4892035 _112681 s t x h1). Qed.
Lemma lem4892038 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892039 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term222 _112681 t x) = (t x).
Proof. exact (@lem4892038 (t x)). Qed.
Lemma lem4892040 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : t x.
Proof. exact (EQ_MP (@lem4892039 _112681 t x) (@lem4892036 _112681 s t x h1)). Qed.
Lemma lem4892043 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892045 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term179 _112681 t x) = (term223 _112681 t x).
Proof. exact (@lem4892043 (t x)). Qed.
Lemma lem4892048 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term223 _112681 t x.
Proof. exact (EQ_MP (@lem4892045 _112681 t x) (@lem4891998 _112681 t x h1)). Qed.
Lemma lem4892051 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : False.
Proof. exact (@lem4892048 _112681 t x h1 (@lem4892040 _112681 s t x h2)). Qed.
Lemma lem4892052 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4892051 _112681 s t x h1 h2). Qed.
Lemma lem4892054 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892055 : term152 = False.
Proof. exact (@lem4892054 False). Qed.
Lemma lem4892056 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892055) (@lem4892052 _112681 s t x h1 h2)). Qed.
Lemma lem4892058 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : s x.
Proof. exact (proj1 (@lem4891933 _112681 s t x h1)). Qed.
Lemma lem4892059 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : term222 _112681 s x.
Proof. exact (fun h0 : term179 _112681 s x => @lem4892058 _112681 s t x h1). Qed.
Lemma lem4892061 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892062 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term222 _112681 s x) = (s x).
Proof. exact (@lem4892061 (s x)). Qed.
Lemma lem4892063 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : s x.
Proof. exact (EQ_MP (@lem4892062 _112681 s x) (@lem4892059 _112681 s t x h1)). Qed.
Lemma lem4892066 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892068 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) : (term179 _112681 s x) = (term223 _112681 s x).
Proof. exact (@lem4892066 (s x)). Qed.
Lemma lem4892071 {_112681 : Type'} (s : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) : term223 _112681 s x.
Proof. exact (EQ_MP (@lem4892068 _112681 s x) (@lem4892004 _112681 s x h1)). Qed.
Lemma lem4892074 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : False.
Proof. exact (@lem4892071 _112681 s x h1 (@lem4892063 _112681 s t x h2)). Qed.
Lemma lem4892075 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4892074 _112681 s t x h1 h2). Qed.
Lemma lem4892077 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892078 : term152 = False.
Proof. exact (@lem4892077 False). Qed.
Lemma lem4892079 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892078) (@lem4892075 _112681 s t x h1 h2)). Qed.
Lemma lem4892081 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : t x.
Proof. exact (proj2 (@lem4891933 _112681 s t x h1)). Qed.
Lemma lem4892082 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : term222 _112681 t x.
Proof. exact (fun h0 : term179 _112681 t x => @lem4892081 _112681 s t x h1). Qed.
Lemma lem4892084 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892085 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term222 _112681 t x) = (t x).
Proof. exact (@lem4892084 (t x)). Qed.
Lemma lem4892086 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : t x.
Proof. exact (EQ_MP (@lem4892085 _112681 t x) (@lem4892082 _112681 s t x h1)). Qed.
Lemma lem4892089 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892091 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) : (term179 _112681 t x) = (term223 _112681 t x).
Proof. exact (@lem4892089 (t x)). Qed.
Lemma lem4892094 {_112681 : Type'} (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) : term223 _112681 t x.
Proof. exact (EQ_MP (@lem4892091 _112681 t x) (@lem4892010 _112681 t x h1)). Qed.
Lemma lem4892097 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : False.
Proof. exact (@lem4892094 _112681 t x h1 (@lem4892086 _112681 s t x h2)). Qed.
Lemma lem4892098 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4892097 _112681 s t x h1 h2). Qed.
Lemma lem4892100 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892101 : term152 = False.
Proof. exact (@lem4892100 False). Qed.
Lemma lem4892102 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892101) (@lem4892098 _112681 s t x h1 h2)). Qed.
Lemma lem4892103 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892102 _112681 s t x h1 h2) (fun h3 : False => @lem4892010 _112681 t x h1)). Qed.
Lemma lem4892104 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892103 _112681 s t x h1 h2) (@lem4892010 _112681 t x h1)). Qed.
Lemma lem4892105 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892079 _112681 s t x h1 h2) (fun h3 : False => @lem4892004 _112681 s x h1)). Qed.
Lemma lem4892106 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892105 _112681 s t x h1 h2) (@lem4892004 _112681 s x h1)). Qed.
Lemma lem4892107 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892056 _112681 s t x h1 h2) (fun h3 : False => @lem4891998 _112681 t x h1)). Qed.
Lemma lem4892108 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892107 _112681 s t x h1 h2) (@lem4891998 _112681 t x h1)). Qed.
Lemma lem4892109 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892033 _112681 s t x h1 h2) (fun h3 : False => @lem4891992 _112681 s x h1)). Qed.
Lemma lem4892110 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892109 _112681 s t x h1 h2) (@lem4891992 _112681 s x h1)). Qed.
Lemma lem4892111 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892104 _112681 s t x h1 h2) (fun h3 : False => @lem4891986 _112681 t x h1)). Qed.
Lemma lem4892112 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892111 _112681 s t x h1 h2) (@lem4891986 _112681 t x h1)). Qed.
Lemma lem4892113 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892106 _112681 s t x h1 h2) (fun h3 : False => @lem4891974 _112681 s x h1)). Qed.
Lemma lem4892114 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892113 _112681 s t x h1 h2) (@lem4891974 _112681 s x h1)). Qed.
Lemma lem4892115 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892108 _112681 s t x h1 h2) (fun h3 : False => @lem4891962 _112681 t x h1)). Qed.
Lemma lem4892116 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892115 _112681 s t x h1 h2) (@lem4891962 _112681 t x h1)). Qed.
Lemma lem4892117 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892110 _112681 s t x h1 h2) (fun h3 : False => @lem4891950 _112681 s x h1)). Qed.
Lemma lem4892118 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892117 _112681 s t x h1 h2) (@lem4891950 _112681 s x h1)). Qed.
Lemma lem4892119 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892112 _112681 s t x h1 h2) (fun h3 : False => @lem4891986 _112681 t x h1)). Qed.
Lemma lem4892120 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892119 _112681 s t x h1 h2) (@lem4891986 _112681 t x h1)). Qed.
Lemma lem4892121 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892114 _112681 s t x h1 h2) (fun h3 : False => @lem4891974 _112681 s x h1)). Qed.
Lemma lem4892122 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term214 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892121 _112681 s t x h1 h2) (@lem4891974 _112681 s x h1)). Qed.
Lemma lem4892123 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : (term179 _112681 t x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 t x => @lem4892116 _112681 s t x h1 h2) (fun h3 : False => @lem4891962 _112681 t x h1)). Qed.
Lemma lem4892124 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 t x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892123 _112681 s t x h1 h2) (@lem4891962 _112681 t x h1)). Qed.
Lemma lem4892125 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : (term179 _112681 s x) = False.
Proof. exact (prop_ext (fun h3 : term179 _112681 s x => @lem4892118 _112681 s t x h1 h2) (fun h3 : False => @lem4891950 _112681 s x h1)). Qed.
Lemma lem4892126 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term179 _112681 s x) (h2 : term217 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892125 _112681 s t x h1 h2) (@lem4891950 _112681 s x h1)). Qed.
Lemma lem4892127 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term214 _112681 s t x) : False.
Proof. exact (or_elim (@lem4891934 _112681 s t x h1) (fun h0 : term179 _112681 s x => @lem4892122 _112681 s t x h0 h1) (fun h0 : term179 _112681 t x => @lem4892120 _112681 s t x h0 h1)). Qed.
Lemma lem4892128 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term217 _112681 s t x) : False.
Proof. exact (or_elim (@lem4891927 _112681 s t x h1) (fun h0 : term179 _112681 s x => @lem4892126 _112681 s t x h0 h1) (fun h0 : term179 _112681 t x => @lem4892124 _112681 s t x h0 h1)). Qed.
Lemma lem4892129 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term205 _112681 s t x) : False.
Proof. exact (or_elim (@lem4891924 _112681 s t x h1) (fun h0 : term217 _112681 s t x => @lem4892128 _112681 s t x h0) (fun h0 : term214 _112681 s t x => @lem4892127 _112681 s t x h0)). Qed.
Lemma lem4892130 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term205 _112681 s t x) : (term205 _112681 s t x) = False.
Proof. exact (prop_ext (fun h2 : term205 _112681 s t x => @lem4892129 _112681 s t x h1) (fun h2 : False => @lem4891824 _112681 s t x h1)). Qed.
Lemma lem4892131 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) (h1 : term205 _112681 s t x) : False.
Proof. exact (EQ_MP (@lem4892130 _112681 s t x h1) (@lem4891824 _112681 s t x h1)). Qed.
Lemma lem4892132 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : term204 _112681 s t x.
Proof. exact (fun h0 : term205 _112681 s t x => @lem4892131 _112681 s t x h0). Qed.
Lemma lem4892133 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (x : _112681) : (term163 _112681 s t x) = (term185 _112681 s t x).
Proof. exact (EQ_MP (@lem4891823 _112681 s t x) (@lem4892132 _112681 s t x)). Qed.
Lemma lem4892138 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term189 _112681 s t.
Proof. exact (fun x : _112681 => @lem4892133 _112681 s t x). Qed.
Lemma lem4892143 {_112681 : Type'} (t : _112681 -> Prop) : term199 _112681 t.
Proof. exact (fun s : _112681 -> Prop => @lem4892138 _112681 s t). Qed.
Lemma lem4892148 {_112681 : Type'} : term203 _112681.
Proof. exact (fun t : _112681 -> Prop => @lem4892143 _112681 t). Qed.
Lemma lem4892149 {_112681 : Type'} : term202 _112681.
Proof. exact (EQ_MP (@lem4891819 _112681) (@lem4892148 _112681)). Qed.
Lemma lem4892150 {_112681 : Type'} (t : _112681 -> Prop) : term224 _112681 t.
Proof. exact (@lem4892149 _112681 t). Qed.
Lemma lem4892151 {_112681 : Type'} (t : _112681 -> Prop) : (term224 _112681 t) = (term198 _112681 t).
Proof. exact (eq_refl (term224 _112681 t)). Qed.
Lemma lem4892152 {_112681 : Type'} (t : _112681 -> Prop) : term198 _112681 t.
Proof. exact (EQ_MP (@lem4892151 _112681 t) (@lem4892150 _112681 t)). Qed.
Lemma lem4892153 {_112681 : Type'} (t : _112681 -> Prop) (s : _112681 -> Prop) : term225 _112681 t s.
Proof. exact (@lem4892152 _112681 t s). Qed.
Lemma lem4892154 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (term225 _112681 t s) = (term190 _112681 s t).
Proof. exact (eq_refl (term225 _112681 t s)). Qed.
Lemma lem4892155 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term190 _112681 s t.
Proof. exact (EQ_MP (@lem4892154 _112681 s t) (@lem4892153 _112681 t s)). Qed.
Lemma lem4892157 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term190 _112681 s t.
Proof. exact (@lem4891724 _112681 s t (@lem4892155 _112681 s t)). Qed.
Lemma lem4892158 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term191 _112681 s t) : False.
Proof. exact (@lem4892157 _112681 s t (@lem4891708 _112681 s t h1)). Qed.
Lemma lem4892159 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term191 _112681 s t) : (term191 _112681 s t) = False.
Proof. exact (prop_ext (fun h2 : term191 _112681 s t => @lem4892158 _112681 s t h1) (fun h2 : False => @lem4891708 _112681 s t h1)). Qed.
Lemma lem4892160 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) (h1 : term191 _112681 s t) : False.
Proof. exact (EQ_MP (@lem4892159 _112681 s t h1) (@lem4891708 _112681 s t h1)). Qed.
Lemma lem4892161 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term190 _112681 s t.
Proof. exact (fun h0 : term191 _112681 s t => @lem4892160 _112681 s t h0). Qed.
Lemma lem4892162 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term189 _112681 s t.
Proof. exact (EQ_MP (@lem4891707 _112681 s t) (@lem4892161 _112681 s t)). Qed.
Lemma lem4892163 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : term158 _112681 s t.
Proof. exact (EQ_MP (@lem4891703 _112681 s t) (@lem4892162 _112681 s t)). Qed.
Lemma lem4892165 {A : Type'} (P : type686 A) : term226 A P.
Proof. exact (@lem4889827 A P). Qed.
Lemma lem4892166 {A : Type'} (P : type686 A) : (term226 A P) = ((term227 A P) = (term228 A P)).
Proof. exact (eq_refl (term226 A P)). Qed.
Lemma lem4892179 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4892180 {_112693 : Type'} (P : type686 _112693) : ((term3 _112693 P) = (term4 _112693 P)) = (term5 _112693 P).
Proof. exact (@lem4892179 ((term3 _112693 P) = (term4 _112693 P))). Qed.
Lemma lem4892181 {_112693 : Type'} (P : type686 _112693) : (term5 _112693 P) = ((term3 _112693 P) = (term4 _112693 P)).
Proof. exact (SYM (@lem4892180 _112693 P)). Qed.
Lemma lem4892182 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term6 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892183 {_112693 : Type'} : term7 _112693.
Proof. exact (@lem3270825 _112693). Qed.
Lemma lem4892187 {_112693 : Type'} (P : type686 _112693) (h1 : term8 _112693 P) : term8 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892188 {_112693 : Type'} (P : type686 _112693) : term9 _112693 P.
Proof. exact (fun h0 : term8 _112693 P => @lem4892187 _112693 P h0). Qed.
Lemma lem4892189 {_112693 : Type'} (P : type686 _112693) (h1 : term9 _112693 P) : term9 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892190 {_112693 : Type'} (P : type686 _112693) (h1 : term8 _112693 P) : term8 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892191 {_112693 : Type'} (P : type686 _112693) (h1 : term8 _112693 P) (h2 : term9 _112693 P) : term8 _112693 P.
Proof. exact (@lem4892189 _112693 P h2 (@lem4892190 _112693 P h1)). Qed.
Lemma lem4892192 {_112693 : Type'} (P : type686 _112693) (h1 : term8 _112693 P) : term10 _112693 P.
Proof. exact (fun h0 : term9 _112693 P => @lem4892191 _112693 P h1 h0). Qed.
Lemma lem4892193 {_112693 : Type'} (P : type686 _112693) (h1 : term9 _112693 P) : term9 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892194 {_112693 : Type'} (P : type686 _112693) (h1 : term8 _112693 P) (h2 : term9 _112693 P) : term8 _112693 P.
Proof. exact (@lem4892192 _112693 P h1 (@lem4892193 _112693 P h2)). Qed.
Lemma lem4892195 {_112693 : Type'} (P : type686 _112693) (h1 : term9 _112693 P) : term9 _112693 P.
Proof. exact (fun h0 : term8 _112693 P => @lem4892194 _112693 P h0 h1). Qed.
Lemma lem4892196 {_112693 : Type'} (P : type686 _112693) : term11 _112693 P.
Proof. exact (fun h0 : term9 _112693 P => @lem4892195 _112693 P h0). Qed.
Lemma lem4892199 {_112693 : Type'} (P : type686 _112693) : term9 _112693 P.
Proof. exact (@lem4892196 _112693 P (@lem4892188 _112693 P)). Qed.
Lemma lem4892200 {_112693 : Type'} (P : type686 _112693) : term9 _112693 P.
Proof. exact (@lem4892199 _112693 P). Qed.
Lemma lem4892216 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4892217 {_112693 : Type'} : (term12 _112693) = (term13 _112693).
Proof. exact (@lem4892216 (term7 _112693)). Qed.
Lemma lem4892222 {_112693 : Type'} (P : type686 _112693) : (term14 _112693 P) = (term14 _112693 P).
Proof. exact (eq_refl (term14 _112693 P)). Qed.
Lemma lem4892223 {_112693 : Type'} (P : type686 _112693) : (term8 _112693 P) = (term15 _112693 P).
Proof. exact (MK_COMB (@lem4892222 _112693 P) (@lem4892217 _112693)). Qed.
Lemma lem4892226 {_112693 : Type'} : (term16 _112693) = (term17 _112693).
Proof. exact (fun_ext (fun P : type686 _112693 => @lem4892223 _112693 P)). Qed.
Lemma lem4892227 {_112693 : Type'} : (@all ((_112693 -> Prop) -> Prop)) = (@all ((_112693 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112693 -> Prop) -> Prop))). Qed.
Lemma lem4892236 {_112693 : Type'} : (term18 _112693) = (term19 _112693).
Proof. exact (MK_COMB (@lem4892227 _112693) (@lem4892226 _112693)). Qed.
Lemma lem4892237 {_112693 : Type'} (s : _112693 -> Prop) : ((term1 _112693 s) = s) = ((term1 _112693 s) = s).
Proof. exact (eq_refl ((term1 _112693 s) = s)). Qed.
Lemma lem4892238 {_112693 : Type'} : (term20 _112693) = (term20 _112693).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892237 _112693 s)). Qed.
Lemma lem4892239 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892240 {_112693 : Type'} : (term7 _112693) = (term7 _112693).
Proof. exact (MK_COMB (@lem4892239 _112693) (@lem4892238 _112693)). Qed.
Lemma lem4892241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892242 {_112693 : Type'} : (term13 _112693) = (term13 _112693).
Proof. exact (MK_COMB (@lem4892241) (@lem4892240 _112693)). Qed.
Lemma lem4892243 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4892244 {_112693 : Type'} (P : type686 _112693) : (term21 _112693 P) = (term21 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892243 _112693 P s)). Qed.
Lemma lem4892245 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892246 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (MK_COMB (@lem4892245 _112693) (@lem4892244 _112693 P)). Qed.
Lemma lem4892247 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term22 _112693 P s) = (term22 _112693 P s).
Proof. exact (eq_refl (term22 _112693 P s)). Qed.
Lemma lem4892248 {_112693 : Type'} (P : type686 _112693) : (term23 _112693 P) = (term23 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892247 _112693 P s)). Qed.
Lemma lem4892249 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892250 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term3 _112693 P).
Proof. exact (MK_COMB (@lem4892249 _112693) (@lem4892248 _112693 P)). Qed.
Lemma lem4892251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892252 {_112693 : Type'} (P : type686 _112693) : (term24 _112693 P) = (term24 _112693 P).
Proof. exact (MK_COMB (@lem4892251) (@lem4892250 _112693 P)). Qed.
Lemma lem4892253 {_112693 : Type'} (P : type686 _112693) : ((term3 _112693 P) = (term4 _112693 P)) = ((term3 _112693 P) = (term4 _112693 P)).
Proof. exact (MK_COMB (@lem4892252 _112693 P) (@lem4892246 _112693 P)). Qed.
Lemma lem4892254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892255 {_112693 : Type'} (P : type686 _112693) : (term6 _112693 P) = (term6 _112693 P).
Proof. exact (MK_COMB (@lem4892254) (@lem4892253 _112693 P)). Qed.
Lemma lem4892256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4892257 {_112693 : Type'} (P : type686 _112693) : (term14 _112693 P) = (term14 _112693 P).
Proof. exact (MK_COMB (@lem4892256) (@lem4892255 _112693 P)). Qed.
Lemma lem4892258 {_112693 : Type'} (P : type686 _112693) : (term15 _112693 P) = (term15 _112693 P).
Proof. exact (MK_COMB (@lem4892257 _112693 P) (@lem4892242 _112693)). Qed.
Lemma lem4892259 {_112693 : Type'} : (term17 _112693) = (term17 _112693).
Proof. exact (fun_ext (fun P : type686 _112693 => @lem4892258 _112693 P)). Qed.
Lemma lem4892260 {_112693 : Type'} : (@all ((_112693 -> Prop) -> Prop)) = (@all ((_112693 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_112693 -> Prop) -> Prop))). Qed.
Lemma lem4892261 {_112693 : Type'} : (term19 _112693) = (term19 _112693).
Proof. exact (MK_COMB (@lem4892260 _112693) (@lem4892259 _112693)). Qed.
Lemma lem4892290 {_112693 : Type'} : (term18 _112693) = (term19 _112693).
Proof. exact (TRANS (@lem4892236 _112693) (@lem4892261 _112693)). Qed.
Lemma lem4892291 {_112693 : Type'} : (term19 _112693) = (term18 _112693).
Proof. exact (SYM (@lem4892290 _112693)). Qed.
Lemma lem4892292 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term6 _112693 P.
Proof. exact (h1). Qed.
Lemma lem4892293 {_112693 : Type'} (h1 : term7 _112693) : term7 _112693.
Proof. exact (h1). Qed.
Lemma lem4892295 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term22 _112693 P s) = (term22 _112693 P s).
Proof. exact (eq_refl (term22 _112693 P s)). Qed.
Lemma lem4892296 {_112693 : Type'} (P : type686 _112693) : (term25 _112693 P) = (term26 _112693 P).
Proof. exact (@lem18392 (_112693 -> Prop) P). Qed.
Lemma lem4892297 {_112693 : Type'} (P : type686 _112693) : (term27 _112693 P) = (term28 _112693 P).
Proof. exact (@lem4892296 _112693 (term23 _112693 P)). Qed.
Lemma lem4892298 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term29 _112693 P s) = (term22 _112693 P s).
Proof. exact (eq_refl (term29 _112693 P s)). Qed.
Lemma lem4892299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892301 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term30 _112693 P s) = (term31 _112693 P s).
Proof. exact (MK_COMB (@lem4892299) (@lem4892298 _112693 P s)). Qed.
Lemma lem4892302 {_112693 : Type'} (P : type686 _112693) : (term32 _112693 P) = (term33 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892301 _112693 P s)). Qed.
Lemma lem4892303 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892304 {_112693 : Type'} (P : type686 _112693) : (term28 _112693 P) = (term34 _112693 P).
Proof. exact (MK_COMB (@lem4892303 _112693) (@lem4892302 _112693 P)). Qed.
Lemma lem4892305 {_112693 : Type'} (P : type686 _112693) : (term27 _112693 P) = (term34 _112693 P).
Proof. exact (TRANS (@lem4892297 _112693 P) (@lem4892304 _112693 P)). Qed.
Lemma lem4892306 {_112693 : Type'} (P : type686 _112693) : (term23 _112693 P) = (term23 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892295 _112693 P s)). Qed.
Lemma lem4892307 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892308 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term3 _112693 P).
Proof. exact (MK_COMB (@lem4892307 _112693) (@lem4892306 _112693 P)). Qed.
Lemma lem4892310 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4892311 {_112693 : Type'} (P : type686 _112693) : (term25 _112693 P) = (term26 _112693 P).
Proof. exact (@lem18392 (_112693 -> Prop) P). Qed.
Lemma lem4892312 {_112693 : Type'} (P : type686 _112693) : (term35 _112693 P) = (term36 _112693 P).
Proof. exact (@lem4892311 _112693 (term21 _112693 P)). Qed.
Lemma lem4892313 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term37 _112693 P s) = (P s).
Proof. exact (eq_refl (term37 _112693 P s)). Qed.
Lemma lem4892314 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892316 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term38 _112693 P s) = (term39 _112693 P s).
Proof. exact (MK_COMB (@lem4892314) (@lem4892313 _112693 P s)). Qed.
Lemma lem4892317 {_112693 : Type'} (P : type686 _112693) : (term40 _112693 P) = (term41 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892316 _112693 P s)). Qed.
Lemma lem4892318 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892319 {_112693 : Type'} (P : type686 _112693) : (term36 _112693 P) = (term26 _112693 P).
Proof. exact (MK_COMB (@lem4892318 _112693) (@lem4892317 _112693 P)). Qed.
Lemma lem4892320 {_112693 : Type'} (P : type686 _112693) : (term35 _112693 P) = (term26 _112693 P).
Proof. exact (TRANS (@lem4892312 _112693 P) (@lem4892319 _112693 P)). Qed.
Lemma lem4892321 {_112693 : Type'} (P : type686 _112693) : (term21 _112693 P) = (term21 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892310 _112693 P s)). Qed.
Lemma lem4892322 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892323 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (MK_COMB (@lem4892322 _112693) (@lem4892321 _112693 P)). Qed.
Lemma lem4892324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892325 {_112693 : Type'} (P : type686 _112693) : (term42 _112693 P) = (term43 _112693 P).
Proof. exact (MK_COMB (@lem4892324) (@lem4892305 _112693 P)). Qed.
Lemma lem4892326 {_112693 : Type'} (P : type686 _112693) : (term44 _112693 P) = (term45 _112693 P).
Proof. exact (MK_COMB (@lem4892325 _112693 P) (@lem4892323 _112693 P)). Qed.
Lemma lem4892327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892328 {_112693 : Type'} (P : type686 _112693) : (term46 _112693 P) = (term46 _112693 P).
Proof. exact (MK_COMB (@lem4892327) (@lem4892308 _112693 P)). Qed.
Lemma lem4892329 {_112693 : Type'} (P : type686 _112693) : (term47 _112693 P) = (term48 _112693 P).
Proof. exact (MK_COMB (@lem4892328 _112693 P) (@lem4892320 _112693 P)). Qed.
Lemma lem4892330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892331 {_112693 : Type'} (P : type686 _112693) : (term49 _112693 P) = (term50 _112693 P).
Proof. exact (MK_COMB (@lem4892330) (@lem4892329 _112693 P)). Qed.
Lemma lem4892332 {_112693 : Type'} (P : type686 _112693) : (term51 _112693 P) = (term52 _112693 P).
Proof. exact (MK_COMB (@lem4892331 _112693 P) (@lem4892326 _112693 P)). Qed.
Lemma lem4892333 {_112693 : Type'} (P : type686 _112693) : (term6 _112693 P) = (term51 _112693 P).
Proof. exact (@lem17646 (term3 _112693 P) (term4 _112693 P)). Qed.
Lemma lem4892334 {_112693 : Type'} (P : type686 _112693) : (term6 _112693 P) = (term52 _112693 P).
Proof. exact (TRANS (@lem4892333 _112693 P) (@lem4892332 _112693 P)). Qed.
Lemma lem4892353 {A : Type'} (P : Prop) (Q : A -> Prop) : (term53 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4892354 {_112693 : Type'} (P : Prop) (Q : type686 _112693) : (term55 _112693 P Q) = (term56 _112693 P Q).
Proof. exact (@lem4892353 (_112693 -> Prop) P Q). Qed.
Lemma lem4892355 {_112693 : Type'} (P : type686 _112693) : (term57 _112693 P) = (term58 _112693 P).
Proof. exact (@lem4892354 _112693 (term3 _112693 P) (term41 _112693 P)). Qed.
Lemma lem4892356 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term59 _112693 P s) = (term39 _112693 P s).
Proof. exact (eq_refl (term59 _112693 P s)). Qed.
Lemma lem4892357 {_112693 : Type'} (P : type686 _112693) : (term60 _112693 P) = (term41 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892356 _112693 P s)). Qed.
Lemma lem4892358 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892359 {_112693 : Type'} (P : type686 _112693) : (term61 _112693 P) = (term26 _112693 P).
Proof. exact (MK_COMB (@lem4892358 _112693) (@lem4892357 _112693 P)). Qed.
Lemma lem4892360 {_112693 : Type'} (P : type686 _112693) : (term46 _112693 P) = (term46 _112693 P).
Proof. exact (eq_refl (term46 _112693 P)). Qed.
Lemma lem4892361 {_112693 : Type'} (P : type686 _112693) : (term57 _112693 P) = (term48 _112693 P).
Proof. exact (MK_COMB (@lem4892360 _112693 P) (@lem4892359 _112693 P)). Qed.
Lemma lem4892362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892363 {_112693 : Type'} (P : type686 _112693) : (term62 _112693 P) = (term63 _112693 P).
Proof. exact (MK_COMB (@lem4892362) (@lem4892361 _112693 P)). Qed.
Lemma lem4892364 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term59 _112693 P s) = (term39 _112693 P s).
Proof. exact (eq_refl (term59 _112693 P s)). Qed.
Lemma lem4892365 {_112693 : Type'} (P : type686 _112693) : (term46 _112693 P) = (term46 _112693 P).
Proof. exact (eq_refl (term46 _112693 P)). Qed.
Lemma lem4892366 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term64 _112693 P s) = (term65 _112693 P s).
Proof. exact (MK_COMB (@lem4892365 _112693 P) (@lem4892364 _112693 P s)). Qed.
Lemma lem4892367 {_112693 : Type'} (P : type686 _112693) : (term66 _112693 P) = (term67 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892366 _112693 P s)). Qed.
Lemma lem4892368 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892369 {_112693 : Type'} (P : type686 _112693) : (term58 _112693 P) = (term68 _112693 P).
Proof. exact (MK_COMB (@lem4892368 _112693) (@lem4892367 _112693 P)). Qed.
Lemma lem4892370 {_112693 : Type'} (P : type686 _112693) : ((term57 _112693 P) = (term58 _112693 P)) = ((term48 _112693 P) = (term68 _112693 P)).
Proof. exact (MK_COMB (@lem4892363 _112693 P) (@lem4892369 _112693 P)). Qed.
Lemma lem4892371 {_112693 : Type'} (P : type686 _112693) : (term48 _112693 P) = (term68 _112693 P).
Proof. exact (EQ_MP (@lem4892370 _112693 P) (@lem4892355 _112693 P)). Qed.
Lemma lem4892372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892373 {_112693 : Type'} (P : type686 _112693) : (term50 _112693 P) = (term69 _112693 P).
Proof. exact (MK_COMB (@lem4892372) (@lem4892371 _112693 P)). Qed.
Lemma lem4892375 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4892376 {_112693 : Type'} (P : type686 _112693) (Q : Prop) : (term72 _112693 P Q) = (term73 _112693 P Q).
Proof. exact (@lem4892375 (_112693 -> Prop) P Q). Qed.
Lemma lem4892377 {_112693 : Type'} (P : type686 _112693) : (term74 _112693 P) = (term75 _112693 P).
Proof. exact (@lem4892376 _112693 (term33 _112693 P) (term4 _112693 P)). Qed.
Lemma lem4892378 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term76 _112693 P s) = (term31 _112693 P s).
Proof. exact (eq_refl (term76 _112693 P s)). Qed.
Lemma lem4892379 {_112693 : Type'} (P : type686 _112693) : (term77 _112693 P) = (term33 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892378 _112693 P s)). Qed.
Lemma lem4892380 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892381 {_112693 : Type'} (P : type686 _112693) : (term78 _112693 P) = (term34 _112693 P).
Proof. exact (MK_COMB (@lem4892380 _112693) (@lem4892379 _112693 P)). Qed.
Lemma lem4892382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892383 {_112693 : Type'} (P : type686 _112693) : (term79 _112693 P) = (term43 _112693 P).
Proof. exact (MK_COMB (@lem4892382) (@lem4892381 _112693 P)). Qed.
Lemma lem4892384 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (eq_refl (term4 _112693 P)). Qed.
Lemma lem4892385 {_112693 : Type'} (P : type686 _112693) : (term74 _112693 P) = (term45 _112693 P).
Proof. exact (MK_COMB (@lem4892383 _112693 P) (@lem4892384 _112693 P)). Qed.
Lemma lem4892386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892387 {_112693 : Type'} (P : type686 _112693) : (term80 _112693 P) = (term81 _112693 P).
Proof. exact (MK_COMB (@lem4892386) (@lem4892385 _112693 P)). Qed.
Lemma lem4892388 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term76 _112693 P s) = (term31 _112693 P s).
Proof. exact (eq_refl (term76 _112693 P s)). Qed.
Lemma lem4892389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892390 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term82 _112693 P s) = (term83 _112693 P s).
Proof. exact (MK_COMB (@lem4892389) (@lem4892388 _112693 P s)). Qed.
Lemma lem4892391 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (eq_refl (term4 _112693 P)). Qed.
Lemma lem4892392 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term84 _112693 s P) = (term85 _112693 s P).
Proof. exact (MK_COMB (@lem4892390 _112693 P s) (@lem4892391 _112693 P)). Qed.
Lemma lem4892393 {_112693 : Type'} (P : type686 _112693) : (term86 _112693 P) = (term87 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892392 _112693 s P)). Qed.
Lemma lem4892394 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892395 {_112693 : Type'} (P : type686 _112693) : (term75 _112693 P) = (term88 _112693 P).
Proof. exact (MK_COMB (@lem4892394 _112693) (@lem4892393 _112693 P)). Qed.
Lemma lem4892396 {_112693 : Type'} (P : type686 _112693) : ((term74 _112693 P) = (term75 _112693 P)) = ((term45 _112693 P) = (term88 _112693 P)).
Proof. exact (MK_COMB (@lem4892387 _112693 P) (@lem4892395 _112693 P)). Qed.
Lemma lem4892397 {_112693 : Type'} (P : type686 _112693) : (term45 _112693 P) = (term88 _112693 P).
Proof. exact (EQ_MP (@lem4892396 _112693 P) (@lem4892377 _112693 P)). Qed.
Lemma lem4892398 {_112693 : Type'} (P : type686 _112693) : (term52 _112693 P) = (term89 _112693 P).
Proof. exact (MK_COMB (@lem4892373 _112693 P) (@lem4892397 _112693 P)). Qed.
Lemma lem4892400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4892401 {_112693 : Type'} (P : type686 _112693) (Q : type686 _112693) : (term92 _112693 P Q) = (term93 _112693 P Q).
Proof. exact (@lem4892400 (_112693 -> Prop) P Q). Qed.
Lemma lem4892402 {_112693 : Type'} (P : type686 _112693) : (term94 _112693 P) = (term95 _112693 P).
Proof. exact (@lem4892401 _112693 (term67 _112693 P) (term87 _112693 P)). Qed.
Lemma lem4892403 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term96 _112693 P s) = (term65 _112693 P s).
Proof. exact (eq_refl (term96 _112693 P s)). Qed.
Lemma lem4892404 {_112693 : Type'} (P : type686 _112693) : (term97 _112693 P) = (term67 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892403 _112693 P s)). Qed.
Lemma lem4892405 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892406 {_112693 : Type'} (P : type686 _112693) : (term98 _112693 P) = (term68 _112693 P).
Proof. exact (MK_COMB (@lem4892405 _112693) (@lem4892404 _112693 P)). Qed.
Lemma lem4892407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892408 {_112693 : Type'} (P : type686 _112693) : (term99 _112693 P) = (term69 _112693 P).
Proof. exact (MK_COMB (@lem4892407) (@lem4892406 _112693 P)). Qed.
Lemma lem4892409 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term100 _112693 P s) = (term85 _112693 s P).
Proof. exact (eq_refl (term100 _112693 P s)). Qed.
Lemma lem4892410 {_112693 : Type'} (P : type686 _112693) : (term101 _112693 P) = (term87 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892409 _112693 s P)). Qed.
Lemma lem4892411 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892412 {_112693 : Type'} (P : type686 _112693) : (term102 _112693 P) = (term88 _112693 P).
Proof. exact (MK_COMB (@lem4892411 _112693) (@lem4892410 _112693 P)). Qed.
Lemma lem4892413 {_112693 : Type'} (P : type686 _112693) : (term94 _112693 P) = (term89 _112693 P).
Proof. exact (MK_COMB (@lem4892408 _112693 P) (@lem4892412 _112693 P)). Qed.
Lemma lem4892414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892415 {_112693 : Type'} (P : type686 _112693) : (term103 _112693 P) = (term104 _112693 P).
Proof. exact (MK_COMB (@lem4892414) (@lem4892413 _112693 P)). Qed.
Lemma lem4892416 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term96 _112693 P s) = (term65 _112693 P s).
Proof. exact (eq_refl (term96 _112693 P s)). Qed.
Lemma lem4892417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892418 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term105 _112693 P s) = (term106 _112693 P s).
Proof. exact (MK_COMB (@lem4892417) (@lem4892416 _112693 P s)). Qed.
Lemma lem4892419 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term100 _112693 P s) = (term85 _112693 s P).
Proof. exact (eq_refl (term100 _112693 P s)). Qed.
Lemma lem4892420 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term107 _112693 P s) = (term108 _112693 s P).
Proof. exact (MK_COMB (@lem4892418 _112693 P s) (@lem4892419 _112693 s P)). Qed.
Lemma lem4892421 {_112693 : Type'} (P : type686 _112693) : (term109 _112693 P) = (term110 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892420 _112693 s P)). Qed.
Lemma lem4892422 {_112693 : Type'} : (@ex (_112693 -> Prop)) = (@ex (_112693 -> Prop)).
Proof. exact (eq_refl (@ex (_112693 -> Prop))). Qed.
Lemma lem4892423 {_112693 : Type'} (P : type686 _112693) : (term95 _112693 P) = (term111 _112693 P).
Proof. exact (MK_COMB (@lem4892422 _112693) (@lem4892421 _112693 P)). Qed.
Lemma lem4892424 {_112693 : Type'} (P : type686 _112693) : ((term94 _112693 P) = (term95 _112693 P)) = ((term89 _112693 P) = (term111 _112693 P)).
Proof. exact (MK_COMB (@lem4892415 _112693 P) (@lem4892423 _112693 P)). Qed.
Lemma lem4892425 {_112693 : Type'} (P : type686 _112693) : (term89 _112693 P) = (term111 _112693 P).
Proof. exact (EQ_MP (@lem4892424 _112693 P) (@lem4892402 _112693 P)). Qed.
Lemma lem4892427 {_112693 : Type'} (P : type686 _112693) : (term52 _112693 P) = (term111 _112693 P).
Proof. exact (TRANS (@lem4892398 _112693 P) (@lem4892425 _112693 P)). Qed.
Lemma lem4892428 {_112693 : Type'} (P : type686 _112693) : (term6 _112693 P) = (term111 _112693 P).
Proof. exact (TRANS (@lem4892334 _112693 P) (@lem4892427 _112693 P)). Qed.
Lemma lem4892429 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term111 _112693 P.
Proof. exact (EQ_MP (@lem4892428 _112693 P) (@lem4892292 _112693 P h1)). Qed.
Lemma lem4892430 {_112693 : Type'} (s : _112693 -> Prop) : ((term1 _112693 s) = s) = ((term1 _112693 s) = s).
Proof. exact (eq_refl ((term1 _112693 s) = s)). Qed.
Lemma lem4892431 {_112693 : Type'} : (term20 _112693) = (term20 _112693).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892430 _112693 s)). Qed.
Lemma lem4892432 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892441 {_112693 : Type'} : (term7 _112693) = (term7 _112693).
Proof. exact (MK_COMB (@lem4892432 _112693) (@lem4892431 _112693)). Qed.
Lemma lem4892442 {_112693 : Type'} (h1 : term7 _112693) : term7 _112693.
Proof. exact (EQ_MP (@lem4892441 _112693) (@lem4892293 _112693 h1)). Qed.
Lemma lem4892443 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term108 _112693 s P) : term108 _112693 s P.
Proof. exact (h1). Qed.
Lemma lem4892456 {_112693 : Type'} (s : _112693 -> Prop) : ((term1 _112693 s) = s) = ((term1 _112693 s) = s).
Proof. exact (eq_refl ((term1 _112693 s) = s)). Qed.
Lemma lem4892457 {_112693 : Type'} : (term20 _112693) = (term20 _112693).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892456 _112693 s)). Qed.
Lemma lem4892458 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892459 {_112693 : Type'} : (term7 _112693) = (term7 _112693).
Proof. exact (MK_COMB (@lem4892458 _112693) (@lem4892457 _112693)). Qed.
Lemma lem4892460 {_112693 : Type'} (h1 : term7 _112693) : term7 _112693.
Proof. exact (EQ_MP (@lem4892459 _112693) (@lem4892442 _112693 h1)). Qed.
Lemma lem4892463 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4892464 {_112693 : Type'} (P : type686 _112693) : (term21 _112693 P) = (term21 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892463 _112693 P s)). Qed.
Lemma lem4892465 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892466 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (MK_COMB (@lem4892465 _112693) (@lem4892464 _112693 P)). Qed.
Lemma lem4892477 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term83 _112693 P s) = (term83 _112693 P s).
Proof. exact (eq_refl (term83 _112693 P s)). Qed.
Lemma lem4892478 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term85 _112693 s P) = (term85 _112693 s P).
Proof. exact (MK_COMB (@lem4892477 _112693 P s) (@lem4892466 _112693 P)). Qed.
Lemma lem4892483 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term39 _112693 P s) = (term39 _112693 P s).
Proof. exact (eq_refl (term39 _112693 P s)). Qed.
Lemma lem4892490 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term22 _112693 P s) = (term22 _112693 P s).
Proof. exact (eq_refl (term22 _112693 P s)). Qed.
Lemma lem4892491 {_112693 : Type'} (P : type686 _112693) : (term23 _112693 P) = (term23 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892490 _112693 P s)). Qed.
Lemma lem4892492 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892493 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term3 _112693 P).
Proof. exact (MK_COMB (@lem4892492 _112693) (@lem4892491 _112693 P)). Qed.
Lemma lem4892494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892495 {_112693 : Type'} (P : type686 _112693) : (term46 _112693 P) = (term46 _112693 P).
Proof. exact (MK_COMB (@lem4892494) (@lem4892493 _112693 P)). Qed.
Lemma lem4892496 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term65 _112693 P s) = (term65 _112693 P s).
Proof. exact (MK_COMB (@lem4892495 _112693 P) (@lem4892483 _112693 P s)). Qed.
Lemma lem4892497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892498 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term106 _112693 P s) = (term106 _112693 P s).
Proof. exact (MK_COMB (@lem4892497) (@lem4892496 _112693 P s)). Qed.
Lemma lem4892499 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) : (term108 _112693 s P) = (term108 _112693 s P).
Proof. exact (MK_COMB (@lem4892498 _112693 P s) (@lem4892478 _112693 s P)). Qed.
Lemma lem4892500 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term108 _112693 s P) : term108 _112693 s P.
Proof. exact (EQ_MP (@lem4892499 _112693 s P) (@lem4892443 _112693 s P h1)). Qed.
Lemma lem4892501 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term65 _112693 P s.
Proof. exact (h1). Qed.
Lemma lem4892502 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term85 _112693 s P.
Proof. exact (h1). Qed.
Lemma lem4892504 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term3 _112693 P.
Proof. exact (proj1 (@lem4892501 _112693 P s h1)). Qed.
Lemma lem4892505 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term4 _112693 P.
Proof. exact (proj2 (@lem4892502 _112693 s P h1)). Qed.
Lemma lem4892508 {_112693 : Type'} (s : _112693 -> Prop) : ((term1 _112693 s) = s) = ((term1 _112693 s) = s).
Proof. exact (eq_refl ((term1 _112693 s) = s)). Qed.
Lemma lem4892509 {_112693 : Type'} : (term20 _112693) = (term20 _112693).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892508 _112693 s)). Qed.
Lemma lem4892510 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892512 {_112693 : Type'} : (term7 _112693) = (term7 _112693).
Proof. exact (MK_COMB (@lem4892510 _112693) (@lem4892509 _112693)). Qed.
Lemma lem4892513 {_112693 : Type'} (h1 : term7 _112693) : term7 _112693.
Proof. exact (EQ_MP (@lem4892512 _112693) (@lem4892460 _112693 h1)). Qed.
Lemma lem4892515 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term22 _112693 P s) = (term22 _112693 P s).
Proof. exact (eq_refl (term22 _112693 P s)). Qed.
Lemma lem4892516 {_112693 : Type'} (P : type686 _112693) : (term23 _112693 P) = (term23 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892515 _112693 P s)). Qed.
Lemma lem4892517 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892519 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term3 _112693 P).
Proof. exact (MK_COMB (@lem4892517 _112693) (@lem4892516 _112693 P)). Qed.
Lemma lem4892520 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term3 _112693 P.
Proof. exact (EQ_MP (@lem4892519 _112693 P) (@lem4892504 _112693 P s h1)). Qed.
Lemma lem4892537 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4892538 {_112693 : Type'} (P : type686 _112693) : (term21 _112693 P) = (term21 _112693 P).
Proof. exact (fun_ext (fun s : _112693 -> Prop => @lem4892537 _112693 P s)). Qed.
Lemma lem4892539 {_112693 : Type'} : (@all (_112693 -> Prop)) = (@all (_112693 -> Prop)).
Proof. exact (eq_refl (@all (_112693 -> Prop))). Qed.
Lemma lem4892541 {_112693 : Type'} (P : type686 _112693) : (term4 _112693 P) = (term4 _112693 P).
Proof. exact (MK_COMB (@lem4892539 _112693) (@lem4892538 _112693 P)). Qed.
Lemma lem4892542 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term4 _112693 P.
Proof. exact (EQ_MP (@lem4892541 _112693 P) (@lem4892505 _112693 s P h1)). Qed.
Lemma lem4892543 {_112693 : Type'} (_60427 : _112693 -> Prop) (h1 : term7 _112693) : term0 _112693 _60427.
Proof. exact (@lem4892513 _112693 h1 _60427). Qed.
Lemma lem4892544 {_112693 : Type'} (_60427 : _112693 -> Prop) : (term0 _112693 _60427) = ((term1 _112693 _60427) = _60427).
Proof. exact (eq_refl (term0 _112693 _60427)). Qed.
Lemma lem4892546 {_112693 : Type'} (_60428 : _112693 -> Prop) (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term29 _112693 P _60428.
Proof. exact (@lem4892520 _112693 P s h1 _60428). Qed.
Lemma lem4892547 {_112693 : Type'} (P : type686 _112693) (_60428 : _112693 -> Prop) : (term29 _112693 P _60428) = (term22 _112693 P _60428).
Proof. exact (eq_refl (term29 _112693 P _60428)). Qed.
Lemma lem4892552 {_112693 : Type'} (_60430 : _112693 -> Prop) (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term37 _112693 P _60430.
Proof. exact (@lem4892542 _112693 s P h1 _60430). Qed.
Lemma lem4892553 {_112693 : Type'} (P : type686 _112693) (_60430 : _112693 -> Prop) : (term37 _112693 P _60430) = (P _60430).
Proof. exact (eq_refl (term37 _112693 P _60430)). Qed.
Lemma lem4892560 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term39 _112693 P s.
Proof. exact (proj2 (@lem4892501 _112693 P s h1)). Qed.
Lemma lem4892564 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term31 _112693 P s.
Proof. exact (proj1 (@lem4892502 _112693 s P h1)). Qed.
Lemma lem4892567 {_112693 : Type'} (P : type686 _112693) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4892568 {_112693 : Type'} (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) (h1 : _60431 = _60432) : _60431 = _60432.
Proof. exact (h1). Qed.
Lemma lem4892569 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) (h1 : _60431 = _60432) : (P _60431) = (P _60432).
Proof. exact (MK_COMB (@lem4892567 _112693 P) (@lem4892568 _112693 _60431 _60432 h1)). Qed.
Lemma lem4892571 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4892572 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : term113 _112693 _60432 P _60431.
Proof. exact (@lem4892571 (P _60432) (P _60431)). Qed.
Lemma lem4892573 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) (h1 : _60431 = _60432) : term114 _112693 _60432 P _60431.
Proof. exact (@lem4892572 _112693 _60432 P _60431 (@lem4892569 _112693 P _60431 _60432 h1)). Qed.
Lemma lem4892574 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : term115 _112693 _60432 P _60431.
Proof. exact (fun h0 : _60431 = _60432 => @lem4892573 _112693 P _60431 _60432 h0). Qed.
Lemma lem4892576 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4892577 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term115 _112693 _60432 P _60431) = (term117 _112693 _60432 P _60431).
Proof. exact (@lem4892576 (_60431 = _60432) (term114 _112693 _60432 P _60431)). Qed.
Lemma lem4892578 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : term117 _112693 _60432 P _60431.
Proof. exact (EQ_MP (@lem4892577 _112693 _60432 P _60431) (@lem4892574 _112693 _60432 P _60431)). Qed.
Lemma lem4892597 {_112693 : Type'} (_60427 : _112693 -> Prop) (h1 : term7 _112693) : (term1 _112693 _60427) = _60427.
Proof. exact (EQ_MP (@lem4892544 _112693 _60427) (@lem4892543 _112693 _60427 h1)). Qed.
Lemma lem4892598 {_112693 : Type'} (_60427 : _112693 -> Prop) (h1 : term7 _112693) : (term1 _112693 _60427) = _60427.
Proof. exact (@lem4892597 _112693 _60427 h1). Qed.
Lemma lem4892599 {_112693 : Type'} (s : _112693 -> Prop) (h1 : term7 _112693) : (term1 _112693 s) = s.
Proof. exact (@lem4892598 _112693 s h1). Qed.
Lemma lem4892600 {_112693 : Type'} (s : _112693 -> Prop) (h1 : term7 _112693) : term118 _112693 s.
Proof. exact (fun h0 : term119 _112693 s => @lem4892599 _112693 s h1). Qed.
Lemma lem4892602 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892603 {_112693 : Type'} (s : _112693 -> Prop) : (term118 _112693 s) = ((term1 _112693 s) = s).
Proof. exact (@lem4892602 ((term1 _112693 s) = s)). Qed.
Lemma lem4892604 {_112693 : Type'} (s : _112693 -> Prop) (h1 : term7 _112693) : (term1 _112693 s) = s.
Proof. exact (EQ_MP (@lem4892603 _112693 s) (@lem4892600 _112693 s h1)). Qed.
Lemma lem4892606 {_112693 : Type'} (_60428 : _112693 -> Prop) (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term22 _112693 P _60428.
Proof. exact (EQ_MP (@lem4892547 _112693 P _60428) (@lem4892546 _112693 _60428 P s h1)). Qed.
Lemma lem4892607 {_112693 : Type'} (_60428 : _112693 -> Prop) (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term22 _112693 P _60428.
Proof. exact (@lem4892606 _112693 _60428 P s h1). Qed.
Lemma lem4892608 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term121 _112693 P s.
Proof. exact (@lem4892607 _112693 (@DIFF _112693 (@UNIV _112693) s) P s h1). Qed.
Lemma lem4892609 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term122 _112693 P s.
Proof. exact (fun h0 : term123 _112693 P s => @lem4892608 _112693 P s h1). Qed.
Lemma lem4892611 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892612 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term122 _112693 P s) = (term121 _112693 P s).
Proof. exact (@lem4892611 (term121 _112693 P s)). Qed.
Lemma lem4892613 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term121 _112693 P s.
Proof. exact (EQ_MP (@lem4892612 _112693 P s) (@lem4892609 _112693 P s h1)). Qed.
Lemma lem4892619 (q : Prop) (p : Prop) (r : Prop) : (term124 p q r) = (term124 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4892620 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term117 _112693 _60432 P _60431) = (term125 _112693 _60432 P _60431).
Proof. exact (@lem4892619 (P _60432) (term126 _112693 _60431 _60432) (term39 _112693 P _60431)). Qed.
Lemma lem4892634 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4892635 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term127 _112693 _60432 P _60431) = (term128 _112693 P _60431 _60432).
Proof. exact (@lem4892634 (term39 _112693 P _60431) (term126 _112693 _60431 _60432)). Qed.
Lemma lem4892643 {_112693 : Type'} (P : type686 _112693) (_60432 : _112693 -> Prop) : (term129 _112693 P _60432) = (term129 _112693 P _60432).
Proof. exact (eq_refl (term129 _112693 P _60432)). Qed.
Lemma lem4892644 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term125 _112693 _60432 P _60431) = (term130 _112693 P _60431 _60432).
Proof. exact (MK_COMB (@lem4892643 _112693 P _60432) (@lem4892635 _112693 P _60431 _60432)). Qed.
Lemma lem4892655 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term117 _112693 _60432 P _60431) = (term130 _112693 P _60431 _60432).
Proof. exact (TRANS (@lem4892620 _112693 _60432 P _60431) (@lem4892644 _112693 P _60431 _60432)). Qed.
Lemma lem4892656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892657 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term131 _112693 _60432 P _60431) = (term132 _112693 P _60431 _60432).
Proof. exact (MK_COMB (@lem4892656) (@lem4892655 _112693 P _60431 _60432)). Qed.
Lemma lem4892671 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4892672 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term127 _112693 _60432 P _60431) = (term128 _112693 P _60431 _60432).
Proof. exact (@lem4892671 (term39 _112693 P _60431) (term126 _112693 _60431 _60432)). Qed.
Lemma lem4892680 {_112693 : Type'} (P : type686 _112693) (_60432 : _112693 -> Prop) : (term129 _112693 P _60432) = (term129 _112693 P _60432).
Proof. exact (eq_refl (term129 _112693 P _60432)). Qed.
Lemma lem4892681 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term125 _112693 _60432 P _60431) = (term130 _112693 P _60431 _60432).
Proof. exact (MK_COMB (@lem4892680 _112693 P _60432) (@lem4892672 _112693 P _60431 _60432)). Qed.
Lemma lem4892692 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : ((term117 _112693 _60432 P _60431) = (term125 _112693 _60432 P _60431)) = ((term130 _112693 P _60431 _60432) = (term130 _112693 P _60431 _60432)).
Proof. exact (MK_COMB (@lem4892657 _112693 P _60431 _60432) (@lem4892681 _112693 P _60431 _60432)). Qed.
Lemma lem4892694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4892695 (x : Prop) : (x = x) = True.
Proof. exact (@lem4892694 Prop x). Qed.
Lemma lem4892696 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : ((term130 _112693 P _60431 _60432) = (term130 _112693 P _60431 _60432)) = True.
Proof. exact (@lem4892695 (term130 _112693 P _60431 _60432)). Qed.
Lemma lem4892697 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : ((term117 _112693 _60432 P _60431) = (term125 _112693 _60432 P _60431)) = True.
Proof. exact (TRANS (@lem4892692 _112693 P _60431 _60432) (@lem4892696 _112693 P _60431 _60432)). Qed.
Lemma lem4892698 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : True = ((term117 _112693 _60432 P _60431) = (term125 _112693 _60432 P _60431)).
Proof. exact (SYM (@lem4892697 _112693 _60432 P _60431)). Qed.
Lemma lem4892699 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term117 _112693 _60432 P _60431) = (term125 _112693 _60432 P _60431).
Proof. exact (EQ_MP (@lem4892698 _112693 _60432 P _60431) (@lem0)). Qed.
Lemma lem4892700 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : term125 _112693 _60432 P _60431.
Proof. exact (EQ_MP (@lem4892699 _112693 _60432 P _60431) (@lem4892578 _112693 _60432 P _60431)). Qed.
Lemma lem4892702 (b : Prop) (a : Prop) : (a \/ b) = (term133 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4892703 {_112693 : Type'} (_60431 : _112693 -> Prop) (P : type686 _112693) (_60432 : _112693 -> Prop) : (term125 _112693 _60432 P _60431) = (term134 _112693 _60431 P _60432).
Proof. exact (@lem4892702 (term127 _112693 _60432 P _60431) (P _60432)). Qed.
Lemma lem4892705 (a : Prop) (b : Prop) : (term135 a b) = (term136 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4892706 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term137 _112693 _60432 P _60431) = (term138 _112693 _60432 P _60431).
Proof. exact (@lem4892705 (term126 _112693 _60431 _60432) (term39 _112693 P _60431)). Qed.
Lemma lem4892708 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4892709 {_112693 : Type'} (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term140 _112693 _60431 _60432) = (_60431 = _60432).
Proof. exact (@lem4892708 (_60431 = _60432)). Qed.
Lemma lem4892710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892711 {_112693 : Type'} (_60431 : _112693 -> Prop) (_60432 : _112693 -> Prop) : (term141 _112693 _60431 _60432) = (term142 _112693 _60431 _60432).
Proof. exact (MK_COMB (@lem4892710) (@lem4892709 _112693 _60431 _60432)). Qed.
Lemma lem4892713 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4892714 {_112693 : Type'} (P : type686 _112693) (_60431 : _112693 -> Prop) : (term143 _112693 P _60431) = (P _60431).
Proof. exact (@lem4892713 (P _60431)). Qed.
Lemma lem4892715 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term138 _112693 _60432 P _60431) = (term144 _112693 _60432 P _60431).
Proof. exact (MK_COMB (@lem4892711 _112693 _60431 _60432) (@lem4892714 _112693 P _60431)). Qed.
Lemma lem4892716 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term137 _112693 _60432 P _60431) = (term144 _112693 _60432 P _60431).
Proof. exact (TRANS (@lem4892706 _112693 _60432 P _60431) (@lem4892715 _112693 _60432 P _60431)). Qed.
Lemma lem4892717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4892718 {_112693 : Type'} (_60432 : _112693 -> Prop) (P : type686 _112693) (_60431 : _112693 -> Prop) : (term145 _112693 _60432 P _60431) = (term146 _112693 _60432 P _60431).
Proof. exact (MK_COMB (@lem4892717) (@lem4892716 _112693 _60432 P _60431)). Qed.
Lemma lem4892719 {_112693 : Type'} (P : type686 _112693) (_60432 : _112693 -> Prop) : (P _60432) = (P _60432).
Proof. exact (eq_refl (P _60432)). Qed.
Lemma lem4892720 {_112693 : Type'} (_60431 : _112693 -> Prop) (P : type686 _112693) (_60432 : _112693 -> Prop) : (term134 _112693 _60431 P _60432) = (term147 _112693 _60431 P _60432).
Proof. exact (MK_COMB (@lem4892718 _112693 _60432 P _60431) (@lem4892719 _112693 P _60432)). Qed.
Lemma lem4892721 {_112693 : Type'} (_60431 : _112693 -> Prop) (P : type686 _112693) (_60432 : _112693 -> Prop) : (term125 _112693 _60432 P _60431) = (term147 _112693 _60431 P _60432).
Proof. exact (TRANS (@lem4892703 _112693 _60431 P _60432) (@lem4892720 _112693 _60431 P _60432)). Qed.
Lemma lem4892723 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : term148 _112693 P s.
Proof. exact (conj (@lem4892604 _112693 s h1) (@lem4892613 _112693 P s h2)). Qed.
Lemma lem4892725 {_112693 : Type'} (_60431 : _112693 -> Prop) (P : type686 _112693) (_60432 : _112693 -> Prop) : term147 _112693 _60431 P _60432.
Proof. exact (EQ_MP (@lem4892721 _112693 _60431 P _60432) (@lem4892700 _112693 _60432 P _60431)). Qed.
Lemma lem4892726 {_112693 : Type'} (_60431 : _112693 -> Prop) (P : type686 _112693) (_60432 : _112693 -> Prop) : term147 _112693 _60431 P _60432.
Proof. exact (@lem4892725 _112693 _60431 P _60432). Qed.
Lemma lem4892727 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : term149 _112693 P s.
Proof. exact (@lem4892726 _112693 (term1 _112693 s) P s). Qed.
Lemma lem4892730 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : P s.
Proof. exact (@lem4892727 _112693 P s (@lem4892723 _112693 P s h1 h2)). Qed.
Lemma lem4892731 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : term150 _112693 P s.
Proof. exact (fun h0 : term39 _112693 P s => @lem4892730 _112693 P s h1 h2). Qed.
Lemma lem4892733 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892734 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term150 _112693 P s) = (P s).
Proof. exact (@lem4892733 (P s)). Qed.
Lemma lem4892735 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : P s.
Proof. exact (EQ_MP (@lem4892734 _112693 P s) (@lem4892731 _112693 P s h1 h2)). Qed.
Lemma lem4892738 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892740 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term39 _112693 P s) = (term151 _112693 P s).
Proof. exact (@lem4892738 (P s)). Qed.
Lemma lem4892743 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term65 _112693 P s) : term151 _112693 P s.
Proof. exact (EQ_MP (@lem4892740 _112693 P s) (@lem4892560 _112693 P s h1)). Qed.
Lemma lem4892746 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : False.
Proof. exact (@lem4892743 _112693 P s h2 (@lem4892735 _112693 P s h1 h2)). Qed.
Lemma lem4892747 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : term152.
Proof. exact (fun h0 : ~ False => @lem4892746 _112693 P s h1 h2). Qed.
Lemma lem4892749 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892750 : term152 = False.
Proof. exact (@lem4892749 False). Qed.
Lemma lem4892751 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : False.
Proof. exact (EQ_MP (@lem4892750) (@lem4892747 _112693 P s h1 h2)). Qed.
Lemma lem4892782 {_112693 : Type'} (_60430 : _112693 -> Prop) (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : P _60430.
Proof. exact (EQ_MP (@lem4892553 _112693 P _60430) (@lem4892552 _112693 _60430 s P h1)). Qed.
Lemma lem4892783 {_112693 : Type'} (_60430 : _112693 -> Prop) (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : P _60430.
Proof. exact (@lem4892782 _112693 _60430 s P h1). Qed.
Lemma lem4892784 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term22 _112693 P s.
Proof. exact (@lem4892783 _112693 (@DIFF _112693 (@UNIV _112693) s) s P h1). Qed.
Lemma lem4892785 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term153 _112693 P s.
Proof. exact (fun h0 : term31 _112693 P s => @lem4892784 _112693 s P h1). Qed.
Lemma lem4892787 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892788 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term153 _112693 P s) = (term22 _112693 P s).
Proof. exact (@lem4892787 (term22 _112693 P s)). Qed.
Lemma lem4892789 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term22 _112693 P s.
Proof. exact (EQ_MP (@lem4892788 _112693 P s) (@lem4892785 _112693 s P h1)). Qed.
Lemma lem4892792 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4892794 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) : (term31 _112693 P s) = (term154 _112693 P s).
Proof. exact (@lem4892792 (term22 _112693 P s)). Qed.
Lemma lem4892797 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term154 _112693 P s.
Proof. exact (EQ_MP (@lem4892794 _112693 P s) (@lem4892564 _112693 s P h1)). Qed.
Lemma lem4892800 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : False.
Proof. exact (@lem4892797 _112693 s P h1 (@lem4892789 _112693 s P h1)). Qed.
Lemma lem4892801 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : term152.
Proof. exact (fun h0 : ~ False => @lem4892800 _112693 s P h1). Qed.
Lemma lem4892803 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4892804 : term152 = False.
Proof. exact (@lem4892803 False). Qed.
Lemma lem4892805 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term85 _112693 s P) : False.
Proof. exact (EQ_MP (@lem4892804) (@lem4892801 _112693 s P h1)). Qed.
Lemma lem4892806 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : (term7 _112693) = False.
Proof. exact (prop_ext (fun h3 : term7 _112693 => @lem4892751 _112693 P s h1 h2) (fun h3 : False => @lem4892513 _112693 h1)). Qed.
Lemma lem4892807 {_112693 : Type'} (P : type686 _112693) (s : _112693 -> Prop) (h1 : term7 _112693) (h2 : term65 _112693 P s) : False.
Proof. exact (EQ_MP (@lem4892806 _112693 P s h1 h2) (@lem4892513 _112693 h1)). Qed.
Lemma lem4892808 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term7 _112693) (h2 : term108 _112693 s P) : False.
Proof. exact (or_elim (@lem4892500 _112693 s P h2) (fun h0 : term65 _112693 P s => @lem4892807 _112693 P s h1 h0) (fun h0 : term85 _112693 s P => @lem4892805 _112693 s P h0)). Qed.
Lemma lem4892809 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term7 _112693) (h2 : term108 _112693 s P) : (term108 _112693 s P) = False.
Proof. exact (prop_ext (fun h3 : term108 _112693 s P => @lem4892808 _112693 s P h1 h2) (fun h3 : False => @lem4892500 _112693 s P h2)). Qed.
Lemma lem4892810 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term7 _112693) (h2 : term108 _112693 s P) : False.
Proof. exact (EQ_MP (@lem4892809 _112693 s P h1 h2) (@lem4892500 _112693 s P h2)). Qed.
Lemma lem4892811 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term7 _112693) (h2 : term108 _112693 s P) : (term7 _112693) = False.
Proof. exact (prop_ext (fun h3 : term7 _112693 => @lem4892810 _112693 s P h1 h2) (fun h3 : False => @lem4892460 _112693 h1)). Qed.
Lemma lem4892812 {_112693 : Type'} (s : _112693 -> Prop) (P : type686 _112693) (h1 : term7 _112693) (h2 : term108 _112693 s P) : False.
Proof. exact (EQ_MP (@lem4892811 _112693 s P h1 h2) (@lem4892460 _112693 h1)). Qed.
Lemma lem4892813 {_112693 : Type'} (P : type686 _112693) (h1 : term7 _112693) (h2 : term6 _112693 P) : False.
Proof. exact (ex_elim (@lem4892429 _112693 P h2) (fun s : _112693 -> Prop => fun h0 : term110 _112693 P s => @lem4892812 _112693 s P h1 h0)). Qed.
Lemma lem4892814 {_112693 : Type'} (P : type686 _112693) (h1 : term7 _112693) (h2 : term6 _112693 P) : (term7 _112693) = False.
Proof. exact (prop_ext (fun h3 : term7 _112693 => @lem4892813 _112693 P h1 h2) (fun h3 : False => @lem4892442 _112693 h1)). Qed.
Lemma lem4892815 {_112693 : Type'} (P : type686 _112693) (h1 : term7 _112693) (h2 : term6 _112693 P) : False.
Proof. exact (EQ_MP (@lem4892814 _112693 P h1 h2) (@lem4892442 _112693 h1)). Qed.
Lemma lem4892816 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term12 _112693.
Proof. exact (fun h0 : term7 _112693 => @lem4892815 _112693 P h0 h1). Qed.
Lemma lem4892817 {_112693 : Type'} : (term12 _112693) = (term13 _112693).
Proof. exact (@lem69 (term7 _112693)). Qed.
Lemma lem4892818 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term13 _112693.
Proof. exact (EQ_MP (@lem4892817 _112693) (@lem4892816 _112693 P h1)). Qed.
Lemma lem4892819 {_112693 : Type'} (P : type686 _112693) : term15 _112693 P.
Proof. exact (fun h0 : term6 _112693 P => @lem4892818 _112693 P h0). Qed.
Lemma lem4892824 {_112693 : Type'} : term19 _112693.
Proof. exact (fun P : type686 _112693 => @lem4892819 _112693 P). Qed.
Lemma lem4892825 {_112693 : Type'} : term18 _112693.
Proof. exact (EQ_MP (@lem4892291 _112693) (@lem4892824 _112693)). Qed.
Lemma lem4892826 {_112693 : Type'} (P : type686 _112693) : term155 _112693 P.
Proof. exact (@lem4892825 _112693 P). Qed.
Lemma lem4892827 {_112693 : Type'} (P : type686 _112693) : (term155 _112693 P) = (term8 _112693 P).
Proof. exact (eq_refl (term155 _112693 P)). Qed.
Lemma lem4892828 {_112693 : Type'} (P : type686 _112693) : term8 _112693 P.
Proof. exact (EQ_MP (@lem4892827 _112693 P) (@lem4892826 _112693 P)). Qed.
Lemma lem4892830 {_112693 : Type'} (P : type686 _112693) : term8 _112693 P.
Proof. exact (@lem4892200 _112693 P (@lem4892828 _112693 P)). Qed.
Lemma lem4892831 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : term12 _112693.
Proof. exact (@lem4892830 _112693 P (@lem4892182 _112693 P h1)). Qed.
Lemma lem4892832 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : False.
Proof. exact (@lem4892831 _112693 P h1 (@lem4892183 _112693)). Qed.
Lemma lem4892833 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : (term6 _112693 P) = False.
Proof. exact (prop_ext (fun h2 : term6 _112693 P => @lem4892832 _112693 P h1) (fun h2 : False => @lem4892182 _112693 P h1)). Qed.
Lemma lem4892834 {_112693 : Type'} (P : type686 _112693) (h1 : term6 _112693 P) : False.
Proof. exact (EQ_MP (@lem4892833 _112693 P h1) (@lem4892182 _112693 P h1)). Qed.
Lemma lem4892835 {_112693 : Type'} (P : type686 _112693) : term5 _112693 P.
Proof. exact (fun h0 : term6 _112693 P => @lem4892834 _112693 P h0). Qed.
Lemma lem4892850 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term156 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4892851 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (s = t) = (term156 _112720 s t).
Proof. exact (@lem4892850 _112720 s t). Qed.
Lemma lem4892852 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : ((term229 _112720 s t) = (term230 _112720 s t)) = (term231 _112720 s t).
Proof. exact (@lem4892851 _112720 (term229 _112720 s t) (term230 _112720 s t)). Qed.
Lemma lem4892861 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term231 _112720 s t) = ((term229 _112720 s t) = (term230 _112720 s t)).
Proof. exact (SYM (@lem4892852 _112720 s t)). Qed.
Lemma lem4892869 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4892870 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term166 _112720 x s t) = (term167 _112720 s x t).
Proof. exact (@lem4892869 _112720 s x t). Qed.
Lemma lem4892871 {_112720 : Type'} (x : _112720) (s : _112720 -> Prop) (t : _112720 -> Prop) : (term232 _112720 x s t) = (term233 _112720 x s t).
Proof. exact (@lem4892870 _112720 (@UNIV _112720) x (@UNION _112720 s t)). Qed.
Lemma lem4892875 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4892876 {_112720 : Type'} (x : _112720) : (@IN _112720 x (@UNIV _112720)) = True.
Proof. exact (@lem4892875 _112720 x). Qed.
Lemma lem4892877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892878 {_112720 : Type'} (x : _112720) : (term171 _112720 x) = (and True).
Proof. exact (MK_COMB (@lem4892877) (@lem4892876 _112720 x)). Qed.
Lemma lem4892880 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term172 A x s t) = (term173 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4892881 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term172 _112720 x s t) = (term173 _112720 s x t).
Proof. exact (@lem4892880 _112720 s x t). Qed.
Lemma lem4892885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4892886 {_112720 : Type'} (P : _112720 -> Prop) (x : _112720) : (@IN _112720 x P) = (P x).
Proof. exact (@lem4892885 _112720 P x). Qed.
Lemma lem4892887 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (@IN _112720 x s) = (s x).
Proof. exact (@lem4892886 _112720 s x). Qed.
Lemma lem4892888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4892889 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term234 _112720 x s) = (term235 _112720 s x).
Proof. exact (MK_COMB (@lem4892888) (@lem4892887 _112720 s x)). Qed.
Lemma lem4892891 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4892892 {_112720 : Type'} (P : _112720 -> Prop) (x : _112720) : (@IN _112720 x P) = (P x).
Proof. exact (@lem4892891 _112720 P x). Qed.
Lemma lem4892893 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (@IN _112720 x t) = (t x).
Proof. exact (@lem4892892 _112720 t x). Qed.
Lemma lem4892894 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term173 _112720 s x t) = (term236 _112720 s t x).
Proof. exact (MK_COMB (@lem4892889 _112720 s x) (@lem4892893 _112720 t x)). Qed.
Lemma lem4892897 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term172 _112720 x s t) = (term236 _112720 s t x).
Proof. exact (TRANS (@lem4892881 _112720 s x t) (@lem4892894 _112720 s t x)). Qed.
Lemma lem4892898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892899 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term237 _112720 x s t) = (term238 _112720 s t x).
Proof. exact (MK_COMB (@lem4892898) (@lem4892897 _112720 s t x)). Qed.
Lemma lem4892900 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term233 _112720 x s t) = (term239 _112720 s t x).
Proof. exact (MK_COMB (@lem4892878 _112720 x) (@lem4892899 _112720 s t x)). Qed.
Lemma lem4892902 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4892903 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term239 _112720 s t x) = (term238 _112720 s t x).
Proof. exact (@lem4892902 (term238 _112720 s t x)). Qed.
Lemma lem4892906 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term233 _112720 x s t) = (term238 _112720 s t x).
Proof. exact (TRANS (@lem4892900 _112720 s t x) (@lem4892903 _112720 s t x)). Qed.
Lemma lem4892907 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term232 _112720 x s t) = (term238 _112720 s t x).
Proof. exact (TRANS (@lem4892871 _112720 x s t) (@lem4892906 _112720 s t x)). Qed.
Lemma lem4892908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4892909 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term240 _112720 x s t) = (term241 _112720 s t x).
Proof. exact (MK_COMB (@lem4892908) (@lem4892907 _112720 s t x)). Qed.
Lemma lem4892911 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term159 A x s t) = (term160 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem4892912 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term159 _112720 x s t) = (term160 _112720 s x t).
Proof. exact (@lem4892911 _112720 s x t). Qed.
Lemma lem4892913 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term242 _112720 x s t) = (term243 _112720 s x t).
Proof. exact (@lem4892912 _112720 (@DIFF _112720 (@UNIV _112720) s) x (@DIFF _112720 (@UNIV _112720) t)). Qed.
Lemma lem4892917 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4892918 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term166 _112720 x s t) = (term167 _112720 s x t).
Proof. exact (@lem4892917 _112720 s x t). Qed.
Lemma lem4892919 {_112720 : Type'} (x : _112720) (s : _112720 -> Prop) : (term176 _112720 x s) = (term177 _112720 x s).
Proof. exact (@lem4892918 _112720 (@UNIV _112720) x s). Qed.
Lemma lem4892923 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4892924 {_112720 : Type'} (x : _112720) : (@IN _112720 x (@UNIV _112720)) = True.
Proof. exact (@lem4892923 _112720 x). Qed.
Lemma lem4892925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892926 {_112720 : Type'} (x : _112720) : (term171 _112720 x) = (and True).
Proof. exact (MK_COMB (@lem4892925) (@lem4892924 _112720 x)). Qed.
Lemma lem4892928 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4892929 {_112720 : Type'} (P : _112720 -> Prop) (x : _112720) : (@IN _112720 x P) = (P x).
Proof. exact (@lem4892928 _112720 P x). Qed.
Lemma lem4892930 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (@IN _112720 x s) = (s x).
Proof. exact (@lem4892929 _112720 s x). Qed.
Lemma lem4892931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892932 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term178 _112720 x s) = (term179 _112720 s x).
Proof. exact (MK_COMB (@lem4892931) (@lem4892930 _112720 s x)). Qed.
Lemma lem4892933 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term177 _112720 x s) = (term180 _112720 s x).
Proof. exact (MK_COMB (@lem4892926 _112720 x) (@lem4892932 _112720 s x)). Qed.
Lemma lem4892935 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4892936 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term180 _112720 s x) = (term179 _112720 s x).
Proof. exact (@lem4892935 (term179 _112720 s x)). Qed.
Lemma lem4892937 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term177 _112720 x s) = (term179 _112720 s x).
Proof. exact (TRANS (@lem4892933 _112720 s x) (@lem4892936 _112720 s x)). Qed.
Lemma lem4892938 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term176 _112720 x s) = (term179 _112720 s x).
Proof. exact (TRANS (@lem4892919 _112720 x s) (@lem4892937 _112720 s x)). Qed.
Lemma lem4892939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892940 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term244 _112720 x s) = (term245 _112720 s x).
Proof. exact (MK_COMB (@lem4892939) (@lem4892938 _112720 s x)). Qed.
Lemma lem4892942 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A x s t) = (term167 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4892943 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (t : _112720 -> Prop) : (term166 _112720 x s t) = (term167 _112720 s x t).
Proof. exact (@lem4892942 _112720 s x t). Qed.
Lemma lem4892944 {_112720 : Type'} (x : _112720) (t : _112720 -> Prop) : (term176 _112720 x t) = (term177 _112720 x t).
Proof. exact (@lem4892943 _112720 (@UNIV _112720) x t). Qed.
Lemma lem4892948 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4892949 {_112720 : Type'} (x : _112720) : (@IN _112720 x (@UNIV _112720)) = True.
Proof. exact (@lem4892948 _112720 x). Qed.
Lemma lem4892950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4892951 {_112720 : Type'} (x : _112720) : (term171 _112720 x) = (and True).
Proof. exact (MK_COMB (@lem4892950) (@lem4892949 _112720 x)). Qed.
Lemma lem4892953 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4892954 {_112720 : Type'} (P : _112720 -> Prop) (x : _112720) : (@IN _112720 x P) = (P x).
Proof. exact (@lem4892953 _112720 P x). Qed.
Lemma lem4892955 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (@IN _112720 x t) = (t x).
Proof. exact (@lem4892954 _112720 t x). Qed.
Lemma lem4892956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4892957 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term178 _112720 x t) = (term179 _112720 t x).
Proof. exact (MK_COMB (@lem4892956) (@lem4892955 _112720 t x)). Qed.
Lemma lem4892958 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term177 _112720 x t) = (term180 _112720 t x).
Proof. exact (MK_COMB (@lem4892951 _112720 x) (@lem4892957 _112720 t x)). Qed.
Lemma lem4892960 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4892961 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term180 _112720 t x) = (term179 _112720 t x).
Proof. exact (@lem4892960 (term179 _112720 t x)). Qed.
Lemma lem4892962 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term177 _112720 x t) = (term179 _112720 t x).
Proof. exact (TRANS (@lem4892958 _112720 t x) (@lem4892961 _112720 t x)). Qed.
Lemma lem4892963 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term176 _112720 x t) = (term179 _112720 t x).
Proof. exact (TRANS (@lem4892944 _112720 x t) (@lem4892962 _112720 t x)). Qed.
Lemma lem4892964 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term243 _112720 s x t) = (term246 _112720 s t x).
Proof. exact (MK_COMB (@lem4892940 _112720 s x) (@lem4892963 _112720 t x)). Qed.
Lemma lem4892967 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term242 _112720 x s t) = (term246 _112720 s t x).
Proof. exact (TRANS (@lem4892913 _112720 s x t) (@lem4892964 _112720 s t x)). Qed.
Lemma lem4892968 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : ((term232 _112720 x s t) = (term242 _112720 x s t)) = ((term238 _112720 s t x) = (term246 _112720 s t x)).
Proof. exact (MK_COMB (@lem4892909 _112720 s t x) (@lem4892967 _112720 s t x)). Qed.
Lemma lem4892971 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term247 _112720 s t) = (term248 _112720 s t).
Proof. exact (fun_ext (fun x : _112720 => @lem4892968 _112720 s t x)). Qed.
Lemma lem4892972 {_112720 : Type'} : (@all _112720) = (@all _112720).
Proof. exact (eq_refl (@all _112720)). Qed.
Lemma lem4892973 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term231 _112720 s t) = (term249 _112720 s t).
Proof. exact (MK_COMB (@lem4892972 _112720) (@lem4892971 _112720 s t)). Qed.
Lemma lem4892978 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term249 _112720 s t) = (term231 _112720 s t).
Proof. exact (SYM (@lem4892973 _112720 s t)). Qed.
Lemma lem4892980 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4892981 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term249 _112720 s t) = (term250 _112720 s t).
Proof. exact (@lem4892980 (term249 _112720 s t)). Qed.
Lemma lem4892982 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term250 _112720 s t) = (term249 _112720 s t).
Proof. exact (SYM (@lem4892981 _112720 s t)). Qed.
Lemma lem4892983 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term251 _112720 s t) : term251 _112720 s t.
Proof. exact (h1). Qed.
Lemma lem4892986 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term250 _112720 s t) : term250 _112720 s t.
Proof. exact (h1). Qed.
Lemma lem4892987 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term252 _112720 s t.
Proof. exact (fun h0 : term250 _112720 s t => @lem4892986 _112720 s t h0). Qed.
Lemma lem4892988 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term252 _112720 s t) : term252 _112720 s t.
Proof. exact (h1). Qed.
Lemma lem4892989 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term250 _112720 s t) : term250 _112720 s t.
Proof. exact (h1). Qed.
Lemma lem4892990 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term250 _112720 s t) (h2 : term252 _112720 s t) : term250 _112720 s t.
Proof. exact (@lem4892988 _112720 s t h2 (@lem4892989 _112720 s t h1)). Qed.
Lemma lem4892991 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term250 _112720 s t) : term253 _112720 s t.
Proof. exact (fun h0 : term252 _112720 s t => @lem4892990 _112720 s t h1 h0). Qed.
Lemma lem4892992 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term252 _112720 s t) : term252 _112720 s t.
Proof. exact (h1). Qed.
Lemma lem4892993 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term250 _112720 s t) (h2 : term252 _112720 s t) : term250 _112720 s t.
Proof. exact (@lem4892991 _112720 s t h1 (@lem4892992 _112720 s t h2)). Qed.
Lemma lem4892994 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term252 _112720 s t) : term252 _112720 s t.
Proof. exact (fun h0 : term250 _112720 s t => @lem4892993 _112720 s t h0 h1). Qed.
Lemma lem4892995 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term254 _112720 s t.
Proof. exact (fun h0 : term252 _112720 s t => @lem4892994 _112720 s t h0). Qed.
Lemma lem4892998 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term252 _112720 s t.
Proof. exact (@lem4892995 _112720 s t (@lem4892987 _112720 s t)). Qed.
Lemma lem4892999 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term252 _112720 s t.
Proof. exact (@lem4892998 _112720 s t). Qed.
Lemma lem4893009 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4893010 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term250 _112720 s t) = (term255 _112720 s t).
Proof. exact (@lem4893009 (term251 _112720 s t)). Qed.
Lemma lem4893012 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4893013 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term255 _112720 s t) = (term249 _112720 s t).
Proof. exact (@lem4893012 (term249 _112720 s t)). Qed.
Lemma lem4893018 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term250 _112720 s t) = (term249 _112720 s t).
Proof. exact (TRANS (@lem4893010 _112720 s t) (@lem4893013 _112720 s t)). Qed.
Lemma lem4893023 {_112720 : Type'} (t : _112720 -> Prop) : (term256 _112720 t) = (term257 _112720 t).
Proof. exact (fun_ext (fun s : _112720 -> Prop => @lem4893018 _112720 s t)). Qed.
Lemma lem4893024 {_112720 : Type'} : (@all (_112720 -> Prop)) = (@all (_112720 -> Prop)).
Proof. exact (eq_refl (@all (_112720 -> Prop))). Qed.
Lemma lem4893025 {_112720 : Type'} (t : _112720 -> Prop) : (term258 _112720 t) = (term259 _112720 t).
Proof. exact (MK_COMB (@lem4893024 _112720) (@lem4893023 _112720 t)). Qed.
Lemma lem4893030 {_112720 : Type'} : (term260 _112720) = (term261 _112720).
Proof. exact (fun_ext (fun t : _112720 -> Prop => @lem4893025 _112720 t)). Qed.
Lemma lem4893031 {_112720 : Type'} : (@all (_112720 -> Prop)) = (@all (_112720 -> Prop)).
Proof. exact (eq_refl (@all (_112720 -> Prop))). Qed.
Lemma lem4893040 {_112720 : Type'} : (term262 _112720) = (term263 _112720).
Proof. exact (MK_COMB (@lem4893031 _112720) (@lem4893030 _112720)). Qed.
Lemma lem4893059 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : ((term238 _112720 s t x) = (term246 _112720 s t x)) = ((term238 _112720 s t x) = (term246 _112720 s t x)).
Proof. exact (eq_refl ((term238 _112720 s t x) = (term246 _112720 s t x))). Qed.
Lemma lem4893060 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term248 _112720 s t) = (term248 _112720 s t).
Proof. exact (fun_ext (fun x : _112720 => @lem4893059 _112720 s t x)). Qed.
Lemma lem4893061 {_112720 : Type'} : (@all _112720) = (@all _112720).
Proof. exact (eq_refl (@all _112720)). Qed.
Lemma lem4893062 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term249 _112720 s t) = (term249 _112720 s t).
Proof. exact (MK_COMB (@lem4893061 _112720) (@lem4893060 _112720 s t)). Qed.
Lemma lem4893063 {_112720 : Type'} (t : _112720 -> Prop) : (term257 _112720 t) = (term257 _112720 t).
Proof. exact (fun_ext (fun s : _112720 -> Prop => @lem4893062 _112720 s t)). Qed.
Lemma lem4893064 {_112720 : Type'} : (@all (_112720 -> Prop)) = (@all (_112720 -> Prop)).
Proof. exact (eq_refl (@all (_112720 -> Prop))). Qed.
Lemma lem4893065 {_112720 : Type'} (t : _112720 -> Prop) : (term259 _112720 t) = (term259 _112720 t).
Proof. exact (MK_COMB (@lem4893064 _112720) (@lem4893063 _112720 t)). Qed.
Lemma lem4893066 {_112720 : Type'} : (term261 _112720) = (term261 _112720).
Proof. exact (fun_ext (fun t : _112720 -> Prop => @lem4893065 _112720 t)). Qed.
Lemma lem4893067 {_112720 : Type'} : (@all (_112720 -> Prop)) = (@all (_112720 -> Prop)).
Proof. exact (eq_refl (@all (_112720 -> Prop))). Qed.
Lemma lem4893068 {_112720 : Type'} : (term263 _112720) = (term263 _112720).
Proof. exact (MK_COMB (@lem4893067 _112720) (@lem4893066 _112720)). Qed.
Lemma lem4893093 {_112720 : Type'} : (term262 _112720) = (term263 _112720).
Proof. exact (TRANS (@lem4893040 _112720) (@lem4893068 _112720)). Qed.
Lemma lem4893094 {_112720 : Type'} : (term263 _112720) = (term262 _112720).
Proof. exact (SYM (@lem4893093 _112720)). Qed.
Lemma lem4893096 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4893097 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : ((term238 _112720 s t x) = (term246 _112720 s t x)) = (term264 _112720 s t x).
Proof. exact (@lem4893096 ((term238 _112720 s t x) = (term246 _112720 s t x))). Qed.
Lemma lem4893098 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term264 _112720 s t x) = ((term238 _112720 s t x) = (term246 _112720 s t x)).
Proof. exact (SYM (@lem4893097 _112720 s t x)). Qed.
Lemma lem4893099 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term265 _112720 s t x) : term265 _112720 s t x.
Proof. exact (h1). Qed.
Lemma lem4893108 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term238 _112720 s t x) = (term246 _112720 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem4893113 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term266 _112720 s t x) = (term236 _112720 s t x).
Proof. exact (@lem16933 (term236 _112720 s t x)). Qed.
Lemma lem4893117 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term207 _112720 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4893121 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term207 _112720 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4893122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4893123 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term267 _112720 s x) = (term235 _112720 s x).
Proof. exact (MK_COMB (@lem4893122) (@lem4893117 _112720 s x)). Qed.
Lemma lem4893124 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term268 _112720 s t x) = (term236 _112720 s t x).
Proof. exact (MK_COMB (@lem4893123 _112720 s x) (@lem4893121 _112720 t x)). Qed.
Lemma lem4893125 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term269 _112720 s t x) = (term268 _112720 s t x).
Proof. exact (@lem17045 (term179 _112720 s x) (term179 _112720 t x)). Qed.
Lemma lem4893126 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term269 _112720 s t x) = (term236 _112720 s t x).
Proof. exact (TRANS (@lem4893125 _112720 s t x) (@lem4893124 _112720 s t x)). Qed.
Lemma lem4893129 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term246 _112720 s t x) = (term246 _112720 s t x).
Proof. exact (eq_refl (term246 _112720 s t x)). Qed.
Lemma lem4893130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4893131 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term270 _112720 s t x) = (term271 _112720 s t x).
Proof. exact (MK_COMB (@lem4893130) (@lem4893113 _112720 s t x)). Qed.
Lemma lem4893132 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term272 _112720 s t x) = (term273 _112720 s t x).
Proof. exact (MK_COMB (@lem4893131 _112720 s t x) (@lem4893129 _112720 s t x)). Qed.
Lemma lem4893133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4893134 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term274 _112720 s t x) = (term275 _112720 s t x).
Proof. exact (MK_COMB (@lem4893133) (@lem4893108 _112720 s t x)). Qed.
Lemma lem4893135 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term276 _112720 s t x) = (term277 _112720 s t x).
Proof. exact (MK_COMB (@lem4893134 _112720 s t x) (@lem4893126 _112720 s t x)). Qed.
Lemma lem4893136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4893137 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term278 _112720 s t x) = (term279 _112720 s t x).
Proof. exact (MK_COMB (@lem4893136) (@lem4893135 _112720 s t x)). Qed.
Lemma lem4893138 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term280 _112720 s t x) = (term281 _112720 s t x).
Proof. exact (MK_COMB (@lem4893137 _112720 s t x) (@lem4893132 _112720 s t x)). Qed.
Lemma lem4893139 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term265 _112720 s t x) = (term280 _112720 s t x).
Proof. exact (@lem17646 (term238 _112720 s t x) (term246 _112720 s t x)). Qed.
Lemma lem4893144 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term265 _112720 s t x) = (term281 _112720 s t x).
Proof. exact (TRANS (@lem4893139 _112720 s t x) (@lem4893138 _112720 s t x)). Qed.
Lemma lem4893199 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term265 _112720 s t x) : term281 _112720 s t x.
Proof. exact (EQ_MP (@lem4893144 _112720 s t x) (@lem4893099 _112720 s t x h1)). Qed.
Lemma lem4893200 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term277 _112720 s t x.
Proof. exact (h1). Qed.
Lemma lem4893201 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term273 _112720 s t x.
Proof. exact (h1). Qed.
Lemma lem4893202 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term236 _112720 s t x.
Proof. exact (proj2 (@lem4893200 _112720 s t x h1)). Qed.
Lemma lem4893203 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term246 _112720 s t x.
Proof. exact (proj1 (@lem4893200 _112720 s t x h1)). Qed.
Lemma lem4893208 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term246 _112720 s t x.
Proof. exact (proj2 (@lem4893201 _112720 s t x h1)). Qed.
Lemma lem4893209 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term236 _112720 s t x.
Proof. exact (proj1 (@lem4893201 _112720 s t x h1)). Qed.
Lemma lem4893225 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893237 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893249 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893261 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893263 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term179 _112720 s x.
Proof. exact (proj1 (@lem4893203 _112720 s t x h1)). Qed.
Lemma lem4893267 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893271 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term179 _112720 t x.
Proof. exact (proj2 (@lem4893203 _112720 s t x h1)). Qed.
Lemma lem4893273 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893275 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term179 _112720 s x.
Proof. exact (proj1 (@lem4893208 _112720 s t x h1)). Qed.
Lemma lem4893279 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893283 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term179 _112720 t x.
Proof. exact (proj2 (@lem4893208 _112720 s t x h1)). Qed.
Lemma lem4893285 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893287 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893288 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : term222 _112720 s x.
Proof. exact (fun h0 : term179 _112720 s x => @lem4893287 _112720 s x h1). Qed.
Lemma lem4893290 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893291 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term222 _112720 s x) = (s x).
Proof. exact (@lem4893290 (s x)). Qed.
Lemma lem4893292 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4893291 _112720 s x) (@lem4893288 _112720 s x h1)). Qed.
Lemma lem4893295 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4893297 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term179 _112720 s x) = (term223 _112720 s x).
Proof. exact (@lem4893295 (s x)). Qed.
Lemma lem4893300 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term223 _112720 s x.
Proof. exact (EQ_MP (@lem4893297 _112720 s x) (@lem4893263 _112720 s t x h1)). Qed.
Lemma lem4893303 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : False.
Proof. exact (@lem4893300 _112720 s t x h2 (@lem4893292 _112720 s x h1)). Qed.
Lemma lem4893304 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4893303 _112720 s t x h1 h2). Qed.
Lemma lem4893306 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893307 : term152 = False.
Proof. exact (@lem4893306 False). Qed.
Lemma lem4893308 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893307) (@lem4893304 _112720 s t x h1 h2)). Qed.
Lemma lem4893310 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893311 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : term222 _112720 t x.
Proof. exact (fun h0 : term179 _112720 t x => @lem4893310 _112720 t x h1). Qed.
Lemma lem4893313 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893314 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term222 _112720 t x) = (t x).
Proof. exact (@lem4893313 (t x)). Qed.
Lemma lem4893315 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4893314 _112720 t x) (@lem4893311 _112720 t x h1)). Qed.
Lemma lem4893318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4893320 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term179 _112720 t x) = (term223 _112720 t x).
Proof. exact (@lem4893318 (t x)). Qed.
Lemma lem4893323 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : term223 _112720 t x.
Proof. exact (EQ_MP (@lem4893320 _112720 t x) (@lem4893271 _112720 s t x h1)). Qed.
Lemma lem4893326 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : False.
Proof. exact (@lem4893323 _112720 s t x h2 (@lem4893315 _112720 t x h1)). Qed.
Lemma lem4893327 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4893326 _112720 s t x h1 h2). Qed.
Lemma lem4893329 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893330 : term152 = False.
Proof. exact (@lem4893329 False). Qed.
Lemma lem4893331 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893330) (@lem4893327 _112720 s t x h1 h2)). Qed.
Lemma lem4893333 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4893334 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : term222 _112720 s x.
Proof. exact (fun h0 : term179 _112720 s x => @lem4893333 _112720 s x h1). Qed.
Lemma lem4893336 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893337 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term222 _112720 s x) = (s x).
Proof. exact (@lem4893336 (s x)). Qed.
Lemma lem4893338 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4893337 _112720 s x) (@lem4893334 _112720 s x h1)). Qed.
Lemma lem4893341 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4893343 {_112720 : Type'} (s : _112720 -> Prop) (x : _112720) : (term179 _112720 s x) = (term223 _112720 s x).
Proof. exact (@lem4893341 (s x)). Qed.
Lemma lem4893346 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term223 _112720 s x.
Proof. exact (EQ_MP (@lem4893343 _112720 s x) (@lem4893275 _112720 s t x h1)). Qed.
Lemma lem4893349 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : False.
Proof. exact (@lem4893346 _112720 s t x h2 (@lem4893338 _112720 s x h1)). Qed.
Lemma lem4893350 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4893349 _112720 s t x h1 h2). Qed.
Lemma lem4893352 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893353 : term152 = False.
Proof. exact (@lem4893352 False). Qed.
Lemma lem4893354 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893353) (@lem4893350 _112720 s t x h1 h2)). Qed.
Lemma lem4893356 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4893357 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : term222 _112720 t x.
Proof. exact (fun h0 : term179 _112720 t x => @lem4893356 _112720 t x h1). Qed.
Lemma lem4893359 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893360 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term222 _112720 t x) = (t x).
Proof. exact (@lem4893359 (t x)). Qed.
Lemma lem4893361 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4893360 _112720 t x) (@lem4893357 _112720 t x h1)). Qed.
Lemma lem4893364 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4893366 {_112720 : Type'} (t : _112720 -> Prop) (x : _112720) : (term179 _112720 t x) = (term223 _112720 t x).
Proof. exact (@lem4893364 (t x)). Qed.
Lemma lem4893369 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : term223 _112720 t x.
Proof. exact (EQ_MP (@lem4893366 _112720 t x) (@lem4893283 _112720 s t x h1)). Qed.
Lemma lem4893372 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : False.
Proof. exact (@lem4893369 _112720 s t x h2 (@lem4893361 _112720 t x h1)). Qed.
Lemma lem4893373 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : term152.
Proof. exact (fun h0 : ~ False => @lem4893372 _112720 s t x h1 h2). Qed.
Lemma lem4893375 (p : Prop) : (term120 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4893376 : term152 = False.
Proof. exact (@lem4893375 False). Qed.
Lemma lem4893377 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893376) (@lem4893373 _112720 s t x h1 h2)). Qed.
Lemma lem4893378 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893377 _112720 s t x h1 h2) (fun h3 : False => @lem4893285 _112720 t x h1)). Qed.
Lemma lem4893379 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893378 _112720 s t x h1 h2) (@lem4893285 _112720 t x h1)). Qed.
Lemma lem4893380 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893354 _112720 s t x h1 h2) (fun h3 : False => @lem4893279 _112720 s x h1)). Qed.
Lemma lem4893381 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893380 _112720 s t x h1 h2) (@lem4893279 _112720 s x h1)). Qed.
Lemma lem4893382 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893331 _112720 s t x h1 h2) (fun h3 : False => @lem4893273 _112720 t x h1)). Qed.
Lemma lem4893383 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893382 _112720 s t x h1 h2) (@lem4893273 _112720 t x h1)). Qed.
Lemma lem4893384 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893308 _112720 s t x h1 h2) (fun h3 : False => @lem4893267 _112720 s x h1)). Qed.
Lemma lem4893385 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893384 _112720 s t x h1 h2) (@lem4893267 _112720 s x h1)). Qed.
Lemma lem4893386 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893379 _112720 s t x h1 h2) (fun h3 : False => @lem4893261 _112720 t x h1)). Qed.
Lemma lem4893387 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893386 _112720 s t x h1 h2) (@lem4893261 _112720 t x h1)). Qed.
Lemma lem4893388 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893381 _112720 s t x h1 h2) (fun h3 : False => @lem4893249 _112720 s x h1)). Qed.
Lemma lem4893389 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893388 _112720 s t x h1 h2) (@lem4893249 _112720 s x h1)). Qed.
Lemma lem4893390 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893383 _112720 s t x h1 h2) (fun h3 : False => @lem4893237 _112720 t x h1)). Qed.
Lemma lem4893391 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893390 _112720 s t x h1 h2) (@lem4893237 _112720 t x h1)). Qed.
Lemma lem4893392 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893385 _112720 s t x h1 h2) (fun h3 : False => @lem4893225 _112720 s x h1)). Qed.
Lemma lem4893393 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893392 _112720 s t x h1 h2) (@lem4893225 _112720 s x h1)). Qed.
Lemma lem4893394 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893387 _112720 s t x h1 h2) (fun h3 : False => @lem4893261 _112720 t x h1)). Qed.
Lemma lem4893395 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893394 _112720 s t x h1 h2) (@lem4893261 _112720 t x h1)). Qed.
Lemma lem4893396 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893389 _112720 s t x h1 h2) (fun h3 : False => @lem4893249 _112720 s x h1)). Qed.
Lemma lem4893397 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term273 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893396 _112720 s t x h1 h2) (@lem4893249 _112720 s x h1)). Qed.
Lemma lem4893398 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem4893391 _112720 s t x h1 h2) (fun h3 : False => @lem4893237 _112720 t x h1)). Qed.
Lemma lem4893399 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : t x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893398 _112720 s t x h1 h2) (@lem4893237 _112720 t x h1)). Qed.
Lemma lem4893400 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4893393 _112720 s t x h1 h2) (fun h3 : False => @lem4893225 _112720 s x h1)). Qed.
Lemma lem4893401 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : s x) (h2 : term277 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893400 _112720 s t x h1 h2) (@lem4893225 _112720 s x h1)). Qed.
Lemma lem4893402 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term273 _112720 s t x) : False.
Proof. exact (or_elim (@lem4893209 _112720 s t x h1) (fun h0 : s x => @lem4893397 _112720 s t x h0 h1) (fun h0 : t x => @lem4893395 _112720 s t x h0 h1)). Qed.
Lemma lem4893403 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term277 _112720 s t x) : False.
Proof. exact (or_elim (@lem4893202 _112720 s t x h1) (fun h0 : s x => @lem4893401 _112720 s t x h0 h1) (fun h0 : t x => @lem4893399 _112720 s t x h0 h1)). Qed.
Lemma lem4893404 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term265 _112720 s t x) : False.
Proof. exact (or_elim (@lem4893199 _112720 s t x h1) (fun h0 : term277 _112720 s t x => @lem4893403 _112720 s t x h0) (fun h0 : term273 _112720 s t x => @lem4893402 _112720 s t x h0)). Qed.
Lemma lem4893405 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term265 _112720 s t x) : (term265 _112720 s t x) = False.
Proof. exact (prop_ext (fun h2 : term265 _112720 s t x => @lem4893404 _112720 s t x h1) (fun h2 : False => @lem4893099 _112720 s t x h1)). Qed.
Lemma lem4893406 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) (h1 : term265 _112720 s t x) : False.
Proof. exact (EQ_MP (@lem4893405 _112720 s t x h1) (@lem4893099 _112720 s t x h1)). Qed.
Lemma lem4893407 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : term264 _112720 s t x.
Proof. exact (fun h0 : term265 _112720 s t x => @lem4893406 _112720 s t x h0). Qed.
Lemma lem4893408 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (x : _112720) : (term238 _112720 s t x) = (term246 _112720 s t x).
Proof. exact (EQ_MP (@lem4893098 _112720 s t x) (@lem4893407 _112720 s t x)). Qed.
Lemma lem4893413 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term249 _112720 s t.
Proof. exact (fun x : _112720 => @lem4893408 _112720 s t x). Qed.
Lemma lem4893418 {_112720 : Type'} (t : _112720 -> Prop) : term259 _112720 t.
Proof. exact (fun s : _112720 -> Prop => @lem4893413 _112720 s t). Qed.
Lemma lem4893423 {_112720 : Type'} : term263 _112720.
Proof. exact (fun t : _112720 -> Prop => @lem4893418 _112720 t). Qed.
Lemma lem4893424 {_112720 : Type'} : term262 _112720.
Proof. exact (EQ_MP (@lem4893094 _112720) (@lem4893423 _112720)). Qed.
Lemma lem4893425 {_112720 : Type'} (t : _112720 -> Prop) : term282 _112720 t.
Proof. exact (@lem4893424 _112720 t). Qed.
Lemma lem4893426 {_112720 : Type'} (t : _112720 -> Prop) : (term282 _112720 t) = (term258 _112720 t).
Proof. exact (eq_refl (term282 _112720 t)). Qed.
Lemma lem4893427 {_112720 : Type'} (t : _112720 -> Prop) : term258 _112720 t.
Proof. exact (EQ_MP (@lem4893426 _112720 t) (@lem4893425 _112720 t)). Qed.
Lemma lem4893428 {_112720 : Type'} (t : _112720 -> Prop) (s : _112720 -> Prop) : term283 _112720 t s.
Proof. exact (@lem4893427 _112720 t s). Qed.
Lemma lem4893429 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term283 _112720 t s) = (term250 _112720 s t).
Proof. exact (eq_refl (term283 _112720 t s)). Qed.
Lemma lem4893430 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term250 _112720 s t.
Proof. exact (EQ_MP (@lem4893429 _112720 s t) (@lem4893428 _112720 t s)). Qed.
Lemma lem4893432 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term250 _112720 s t.
Proof. exact (@lem4892999 _112720 s t (@lem4893430 _112720 s t)). Qed.
Lemma lem4893433 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term251 _112720 s t) : False.
Proof. exact (@lem4893432 _112720 s t (@lem4892983 _112720 s t h1)). Qed.
Lemma lem4893434 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term251 _112720 s t) : (term251 _112720 s t) = False.
Proof. exact (prop_ext (fun h2 : term251 _112720 s t => @lem4893433 _112720 s t h1) (fun h2 : False => @lem4892983 _112720 s t h1)). Qed.
Lemma lem4893435 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) (h1 : term251 _112720 s t) : False.
Proof. exact (EQ_MP (@lem4893434 _112720 s t h1) (@lem4892983 _112720 s t h1)). Qed.
Lemma lem4893436 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term250 _112720 s t.
Proof. exact (fun h0 : term251 _112720 s t => @lem4893435 _112720 s t h0). Qed.
Lemma lem4893437 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term249 _112720 s t.
Proof. exact (EQ_MP (@lem4892982 _112720 s t) (@lem4893436 _112720 s t)). Qed.
Lemma lem4893438 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : term231 _112720 s t.
Proof. exact (EQ_MP (@lem4892978 _112720 s t) (@lem4893437 _112720 s t)). Qed.
Lemma lem4893440 {A : Type'} (P : type686 A) : term284 A P.
Proof. exact (@lem4879380 A P). Qed.
Lemma lem4893441 {A : Type'} (P : type686 A) : (term284 A P) = (term285 A P).
Proof. exact (eq_refl (term284 A P)). Qed.
Lemma lem4893442 {A : Type'} (P : type686 A) : term285 A P.
Proof. exact (EQ_MP (@lem4893441 A P) (@lem4893440 A P)). Qed.
Lemma lem4893443 {A : Type'} (P : type686 A) (s : A -> Prop) : term286 A P s.
Proof. exact (@lem4893442 A P s). Qed.
Lemma lem4893444 {A : Type'} (P : type686 A) (s : A -> Prop) : (term286 A P s) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s)).
Proof. exact (eq_refl (term286 A P s)). Qed.
Lemma lem4893465 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4893444 A P s) (@lem4893443 A P s)). Qed.
Lemma lem4893466 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (@lem4893465 A P s). Qed.
Lemma lem4893467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4893468 {A : Type'} (P : type686 A) (s : A -> Prop) : (term288 A P s) = (term289 A P s).
Proof. exact (MK_COMB (@lem4893467) (@lem4893466 A P s)). Qed.
Lemma lem4893470 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4893444 A P s) (@lem4893443 A P s)). Qed.
Lemma lem4893471 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (@lem4893470 A P s). Qed.
Lemma lem4893472 {A : Type'} (P : type686 A) (t : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P t) = (term287 A P t).
Proof. exact (@lem4893471 A P t). Qed.
Lemma lem4893473 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term290 A s P t) = (term291 A s P t).
Proof. exact (MK_COMB (@lem4893468 A P s) (@lem4893472 A P t)). Qed.
Lemma lem4893474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4893475 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term292 A s P t) = (term293 A s P t).
Proof. exact (MK_COMB (@lem4893474) (@lem4893473 A s P t)). Qed.
Lemma lem4893477 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4893444 A P s) (@lem4893443 A P s)). Qed.
Lemma lem4893478 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (@lem4893477 A P s). Qed.
Lemma lem4893479 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term294 A P s t) = (term295 A P s t).
Proof. exact (@lem4893478 A P (@UNION A s t)). Qed.
Lemma lem4893480 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term296 A P s t) = (term297 A P s t).
Proof. exact (MK_COMB (@lem4893475 A s P t) (@lem4893479 A P s t)). Qed.
Lemma lem4893481 {A : Type'} (P : type686 A) (s : A -> Prop) : (term298 A P s) = (term299 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893480 A P s t)). Qed.
Lemma lem4893482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893483 {A : Type'} (P : type686 A) (s : A -> Prop) : (term300 A P s) = (term301 A P s).
Proof. exact (MK_COMB (@lem4893482 A) (@lem4893481 A P s)). Qed.
Lemma lem4893484 {A : Type'} (P : type686 A) : (term302 A P) = (term303 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893483 A P s)). Qed.
Lemma lem4893485 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893486 {A : Type'} (P : type686 A) : (term304 A P) = (term305 A P).
Proof. exact (MK_COMB (@lem4893485 A) (@lem4893484 A P)). Qed.
Lemma lem4893487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893488 {A : Type'} (P : type686 A) : (term306 A P) = (term307 A P).
Proof. exact (MK_COMB (@lem4893487) (@lem4893486 A P)). Qed.
Lemma lem4893502 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (EQ_MP (@lem4893444 A P s) (@lem4893443 A P s)). Qed.
Lemma lem4893503 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term287 A P s).
Proof. exact (@lem4893502 A P s). Qed.
Lemma lem4893504 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term294 A P s t) = (term295 A P s t).
Proof. exact (@lem4893503 A P (@UNION A s t)). Qed.
Lemma lem4893505 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4893506 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term309 A P s t) = (term310 A P s t).
Proof. exact (MK_COMB (@lem4893505 A s P t) (@lem4893504 A P s t)). Qed.
Lemma lem4893507 {A : Type'} (P : type686 A) (s : A -> Prop) : (term311 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893506 A P s t)). Qed.
Lemma lem4893508 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893509 {A : Type'} (P : type686 A) (s : A -> Prop) : (term313 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4893508 A) (@lem4893507 A P s)). Qed.
Lemma lem4893510 {A : Type'} (P : type686 A) : (term315 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893509 A P s)). Qed.
Lemma lem4893511 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893512 {A : Type'} (P : type686 A) : (term317 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4893511 A) (@lem4893510 A P)). Qed.
Lemma lem4893513 {A : Type'} (P : type686 A) : ((term304 A P) = (term317 A P)) = ((term305 A P) = (term318 A P)).
Proof. exact (MK_COMB (@lem4893488 A P) (@lem4893512 A P)). Qed.
Lemma lem4893514 {A : Type'} : (term319 A) = (term320 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4893513 A P)). Qed.
Lemma lem4893515 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4893516 {A : Type'} : (term321 A) = (term322 A).
Proof. exact (MK_COMB (@lem4893515 A) (@lem4893514 A)). Qed.
Lemma lem4893517 {A : Type'} : (term322 A) = (term321 A).
Proof. exact (SYM (@lem4893516 A)). Qed.
Lemma lem4893537 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term229 _112720 s t) = (term230 _112720 s t).
Proof. exact (EQ_MP (@lem4892861 _112720 s t) (@lem4893438 _112720 s t)). Qed.
Lemma lem4893538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term229 A s t) = (term230 A s t).
Proof. exact (@lem4893537 A s t). Qed.
Lemma lem4893539 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4893540 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A P s t) = (term324 A P s t).
Proof. exact (MK_COMB (@lem4893539 A P) (@lem4893538 A s t)). Qed.
Lemma lem4893541 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term293 A s P t) = (term293 A s P t).
Proof. exact (eq_refl (term293 A s P t)). Qed.
Lemma lem4893542 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term297 A P s t) = (term325 A P s t).
Proof. exact (MK_COMB (@lem4893541 A s P t) (@lem4893540 A P s t)). Qed.
Lemma lem4893545 {A : Type'} (P : type686 A) (s : A -> Prop) : (term299 A P s) = (term326 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893542 A P s t)). Qed.
Lemma lem4893546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893547 {A : Type'} (P : type686 A) (s : A -> Prop) : (term301 A P s) = (term327 A P s).
Proof. exact (MK_COMB (@lem4893546 A) (@lem4893545 A P s)). Qed.
Lemma lem4893552 {A : Type'} (P : type686 A) : (term303 A P) = (term328 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893547 A P s)). Qed.
Lemma lem4893553 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893554 {A : Type'} (P : type686 A) : (term305 A P) = (term329 A P).
Proof. exact (MK_COMB (@lem4893553 A) (@lem4893552 A P)). Qed.
Lemma lem4893559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893560 {A : Type'} (P : type686 A) : (term307 A P) = (term330 A P).
Proof. exact (MK_COMB (@lem4893559) (@lem4893554 A P)). Qed.
Lemma lem4893574 {_112720 : Type'} (s : _112720 -> Prop) (t : _112720 -> Prop) : (term229 _112720 s t) = (term230 _112720 s t).
Proof. exact (EQ_MP (@lem4892861 _112720 s t) (@lem4893438 _112720 s t)). Qed.
Lemma lem4893575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term229 A s t) = (term230 A s t).
Proof. exact (@lem4893574 A s t). Qed.
Lemma lem4893576 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4893577 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A P s t) = (term324 A P s t).
Proof. exact (MK_COMB (@lem4893576 A P) (@lem4893575 A s t)). Qed.
Lemma lem4893578 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4893579 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term310 A P s t) = (term331 A P s t).
Proof. exact (MK_COMB (@lem4893578 A s P t) (@lem4893577 A P s t)). Qed.
Lemma lem4893582 {A : Type'} (P : type686 A) (s : A -> Prop) : (term312 A P s) = (term332 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893579 A P s t)). Qed.
Lemma lem4893583 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893584 {A : Type'} (P : type686 A) (s : A -> Prop) : (term314 A P s) = (term333 A P s).
Proof. exact (MK_COMB (@lem4893583 A) (@lem4893582 A P s)). Qed.
Lemma lem4893589 {A : Type'} (P : type686 A) : (term316 A P) = (term334 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893584 A P s)). Qed.
Lemma lem4893590 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893591 {A : Type'} (P : type686 A) : (term318 A P) = (term335 A P).
Proof. exact (MK_COMB (@lem4893590 A) (@lem4893589 A P)). Qed.
Lemma lem4893596 {A : Type'} (P : type686 A) : ((term305 A P) = (term318 A P)) = ((term329 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4893560 A P) (@lem4893591 A P)). Qed.
Lemma lem4893599 {A : Type'} : (term320 A) = (term336 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4893596 A P)). Qed.
Lemma lem4893600 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4893601 {A : Type'} : (term322 A) = (term337 A).
Proof. exact (MK_COMB (@lem4893600 A) (@lem4893599 A)). Qed.
Lemma lem4893606 {A : Type'} : (term337 A) = (term322 A).
Proof. exact (SYM (@lem4893601 A)). Qed.
Lemma lem4893634 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term4 _112693 P).
Proof. exact (EQ_MP (@lem4892181 _112693 P) (@lem4892835 _112693 P)). Qed.
Lemma lem4893635 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4893634 A P). Qed.
Lemma lem4893636 {A : Type'} (P : type686 A) : (term338 A P) = (term339 A P).
Proof. exact (@lem4893635 A (term340 A P)). Qed.
Lemma lem4893637 {A : Type'} (P : type686 A) (s : A -> Prop) : (term341 A P s) = (term327 A P s).
Proof. exact (eq_refl (term341 A P s)). Qed.
Lemma lem4893638 {A : Type'} (P : type686 A) : (term342 A P) = (term328 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893637 A P s)). Qed.
Lemma lem4893639 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893640 {A : Type'} (P : type686 A) : (term338 A P) = (term329 A P).
Proof. exact (MK_COMB (@lem4893639 A) (@lem4893638 A P)). Qed.
Lemma lem4893641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893642 {A : Type'} (P : type686 A) : (term343 A P) = (term330 A P).
Proof. exact (MK_COMB (@lem4893641) (@lem4893640 A P)). Qed.
Lemma lem4893643 {A : Type'} (P : type686 A) (s : A -> Prop) : (term344 A P s) = (term345 A P s).
Proof. exact (eq_refl (term344 A P s)). Qed.
Lemma lem4893644 {A : Type'} (P : type686 A) : (term346 A P) = (term340 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893643 A P s)). Qed.
Lemma lem4893645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893646 {A : Type'} (P : type686 A) : (term339 A P) = (term347 A P).
Proof. exact (MK_COMB (@lem4893645 A) (@lem4893644 A P)). Qed.
Lemma lem4893647 {A : Type'} (P : type686 A) : ((term338 A P) = (term339 A P)) = ((term329 A P) = (term347 A P)).
Proof. exact (MK_COMB (@lem4893642 A P) (@lem4893646 A P)). Qed.
Lemma lem4893648 {A : Type'} (P : type686 A) : (term329 A P) = (term347 A P).
Proof. exact (EQ_MP (@lem4893647 A P) (@lem4893636 A P)). Qed.
Lemma lem4893674 {_112693 : Type'} (P : type686 _112693) : (term3 _112693 P) = (term4 _112693 P).
Proof. exact (EQ_MP (@lem4892181 _112693 P) (@lem4892835 _112693 P)). Qed.
Lemma lem4893675 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4893674 A P). Qed.
Lemma lem4893676 {A : Type'} (P : type686 A) (s : A -> Prop) : (term348 A P s) = (term349 A P s).
Proof. exact (@lem4893675 A (term350 A P s)). Qed.
Lemma lem4893677 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term351 A P s t) = (term352 A P s t).
Proof. exact (eq_refl (term351 A P s t)). Qed.
Lemma lem4893678 {A : Type'} (P : type686 A) (s : A -> Prop) : (term353 A P s) = (term354 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893677 A P s t)). Qed.
Lemma lem4893679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893680 {A : Type'} (P : type686 A) (s : A -> Prop) : (term348 A P s) = (term345 A P s).
Proof. exact (MK_COMB (@lem4893679 A) (@lem4893678 A P s)). Qed.
Lemma lem4893681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893682 {A : Type'} (P : type686 A) (s : A -> Prop) : (term355 A P s) = (term356 A P s).
Proof. exact (MK_COMB (@lem4893681) (@lem4893680 A P s)). Qed.
Lemma lem4893683 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term357 A P s t) = (term358 A P s t).
Proof. exact (eq_refl (term357 A P s t)). Qed.
Lemma lem4893684 {A : Type'} (P : type686 A) (s : A -> Prop) : (term359 A P s) = (term350 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893683 A P s t)). Qed.
Lemma lem4893685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893686 {A : Type'} (P : type686 A) (s : A -> Prop) : (term349 A P s) = (term360 A P s).
Proof. exact (MK_COMB (@lem4893685 A) (@lem4893684 A P s)). Qed.
Lemma lem4893687 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term348 A P s) = (term349 A P s)) = ((term345 A P s) = (term360 A P s)).
Proof. exact (MK_COMB (@lem4893682 A P s) (@lem4893686 A P s)). Qed.
Lemma lem4893688 {A : Type'} (P : type686 A) (s : A -> Prop) : (term345 A P s) = (term360 A P s).
Proof. exact (EQ_MP (@lem4893687 A P s) (@lem4893676 A P s)). Qed.
Lemma lem4893713 {A : Type'} (P : type686 A) : (term340 A P) = (term361 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893688 A P s)). Qed.
Lemma lem4893714 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893715 {A : Type'} (P : type686 A) : (term347 A P) = (term362 A P).
Proof. exact (MK_COMB (@lem4893714 A) (@lem4893713 A P)). Qed.
Lemma lem4893736 {A : Type'} (P : type686 A) : (term329 A P) = (term362 A P).
Proof. exact (TRANS (@lem4893648 A P) (@lem4893715 A P)). Qed.
Lemma lem4893737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893738 {A : Type'} (P : type686 A) : (term330 A P) = (term363 A P).
Proof. exact (MK_COMB (@lem4893737) (@lem4893736 A P)). Qed.
Lemma lem4893783 {A : Type'} (P : type686 A) : (term335 A P) = (term335 A P).
Proof. exact (eq_refl (term335 A P)). Qed.
Lemma lem4893784 {A : Type'} (P : type686 A) : ((term329 A P) = (term335 A P)) = ((term362 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4893738 A P) (@lem4893783 A P)). Qed.
Lemma lem4893787 {A : Type'} : (term336 A) = (term364 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4893784 A P)). Qed.
Lemma lem4893788 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4893789 {A : Type'} : (term337 A) = (term365 A).
Proof. exact (MK_COMB (@lem4893788 A) (@lem4893787 A)). Qed.
Lemma lem4893810 {A : Type'} : (term365 A) = (term337 A).
Proof. exact (SYM (@lem4893789 A)). Qed.
Lemma lem4893818 {A : Type'} (P : type686 A) : (term227 A P) = (term228 A P).
Proof. exact (EQ_MP (@lem4892166 A P) (@lem4892165 A P)). Qed.
Lemma lem4893819 {A : Type'} (P : type686 A) : (term227 A P) = (term228 A P).
Proof. exact (@lem4893818 A P). Qed.
Lemma lem4893820 {A : Type'} (P : type686 A) : (term362 A P) = (term366 A P).
Proof. exact (@lem4893819 A (term23 A P)). Qed.
Lemma lem4893834 {A B : Type'} (f : A -> B) (y : A) : (term367 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4893835 {A : Type'} (f : type686 A) (y : A -> Prop) : (term37 A f y) = (f y).
Proof. exact (@lem4893834 (A -> Prop) Prop f y). Qed.
Lemma lem4893836 {A : Type'} (P : type686 A) (s : A -> Prop) : (term368 A P s) = (term29 A P s).
Proof. exact (@lem4893835 A (term23 A P) s). Qed.
Lemma lem4893837 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4893838 {A : Type'} (P : type686 A) : (term369 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893837 A P s)). Qed.
Lemma lem4893839 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4893840 {A : Type'} (P : type686 A) (s : A -> Prop) : (term368 A P s) = (term29 A P s).
Proof. exact (MK_COMB (@lem4893838 A P) (@lem4893839 A s)). Qed.
Lemma lem4893841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893842 {A : Type'} (P : type686 A) (s : A -> Prop) : (term370 A P s) = (term371 A P s).
Proof. exact (MK_COMB (@lem4893841) (@lem4893840 A P s)). Qed.
Lemma lem4893843 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4893844 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term368 A P s) = (term29 A P s)) = ((term29 A P s) = (term22 A P s)).
Proof. exact (MK_COMB (@lem4893842 A P s) (@lem4893843 A P s)). Qed.
Lemma lem4893845 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (EQ_MP (@lem4893844 A P s) (@lem4893836 A P s)). Qed.
Lemma lem4893846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4893847 {A : Type'} (P : type686 A) (s : A -> Prop) : (term372 A P s) = (term373 A P s).
Proof. exact (MK_COMB (@lem4893846) (@lem4893845 A P s)). Qed.
Lemma lem4893849 {A B : Type'} (f : A -> B) (y : A) : (term367 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4893850 {A : Type'} (f : type686 A) (y : A -> Prop) : (term37 A f y) = (f y).
Proof. exact (@lem4893849 (A -> Prop) Prop f y). Qed.
Lemma lem4893851 {A : Type'} (P : type686 A) (t : A -> Prop) : (term368 A P t) = (term29 A P t).
Proof. exact (@lem4893850 A (term23 A P) t). Qed.
Lemma lem4893852 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term22 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4893853 {A : Type'} (P : type686 A) : (term369 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893852 A P s)). Qed.
Lemma lem4893854 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4893855 {A : Type'} (P : type686 A) (t : A -> Prop) : (term368 A P t) = (term29 A P t).
Proof. exact (MK_COMB (@lem4893853 A P) (@lem4893854 A t)). Qed.
Lemma lem4893856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893857 {A : Type'} (P : type686 A) (t : A -> Prop) : (term370 A P t) = (term371 A P t).
Proof. exact (MK_COMB (@lem4893856) (@lem4893855 A P t)). Qed.
Lemma lem4893858 {A : Type'} (P : type686 A) (t : A -> Prop) : (term29 A P t) = (term22 A P t).
Proof. exact (eq_refl (term29 A P t)). Qed.
Lemma lem4893859 {A : Type'} (P : type686 A) (t : A -> Prop) : ((term368 A P t) = (term29 A P t)) = ((term29 A P t) = (term22 A P t)).
Proof. exact (MK_COMB (@lem4893857 A P t) (@lem4893858 A P t)). Qed.
Lemma lem4893860 {A : Type'} (P : type686 A) (t : A -> Prop) : (term29 A P t) = (term22 A P t).
Proof. exact (EQ_MP (@lem4893859 A P t) (@lem4893851 A P t)). Qed.
Lemma lem4893861 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term374 A s P t) = (term375 A s P t).
Proof. exact (MK_COMB (@lem4893847 A P s) (@lem4893860 A P t)). Qed.
Lemma lem4893864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4893865 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term376 A s P t) = (term377 A s P t).
Proof. exact (MK_COMB (@lem4893864) (@lem4893861 A s P t)). Qed.
Lemma lem4893866 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term378 A P s t) = (term378 A P s t).
Proof. exact (eq_refl (term378 A P s t)). Qed.
Lemma lem4893867 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term379 A P s t) = (term380 A P s t).
Proof. exact (MK_COMB (@lem4893865 A s P t) (@lem4893866 A P s t)). Qed.
Lemma lem4893870 {A : Type'} (P : type686 A) (s : A -> Prop) : (term381 A P s) = (term382 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893867 A P s t)). Qed.
Lemma lem4893871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893872 {A : Type'} (P : type686 A) (s : A -> Prop) : (term383 A P s) = (term384 A P s).
Proof. exact (MK_COMB (@lem4893871 A) (@lem4893870 A P s)). Qed.
Lemma lem4893877 {A : Type'} (P : type686 A) : (term385 A P) = (term386 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893872 A P s)). Qed.
Lemma lem4893878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893879 {A : Type'} (P : type686 A) : (term366 A P) = (term387 A P).
Proof. exact (MK_COMB (@lem4893878 A) (@lem4893877 A P)). Qed.
Lemma lem4893884 {A : Type'} (P : type686 A) : (term362 A P) = (term387 A P).
Proof. exact (TRANS (@lem4893820 A P) (@lem4893879 A P)). Qed.
Lemma lem4893885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893886 {A : Type'} (P : type686 A) : (term363 A P) = (term388 A P).
Proof. exact (MK_COMB (@lem4893885) (@lem4893884 A P)). Qed.
Lemma lem4893899 {A : Type'} (P : type686 A) : (term335 A P) = (term335 A P).
Proof. exact (eq_refl (term335 A P)). Qed.
Lemma lem4893900 {A : Type'} (P : type686 A) : ((term362 A P) = (term335 A P)) = ((term387 A P) = (term335 A P)).
Proof. exact (MK_COMB (@lem4893886 A P) (@lem4893899 A P)). Qed.
Lemma lem4893903 {A : Type'} : (term364 A) = (term389 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4893900 A P)). Qed.
Lemma lem4893904 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4893905 {A : Type'} : (term365 A) = (term390 A).
Proof. exact (MK_COMB (@lem4893904 A) (@lem4893903 A)). Qed.
Lemma lem4893910 {A : Type'} : (term390 A) = (term365 A).
Proof. exact (SYM (@lem4893905 A)). Qed.
Lemma lem4893930 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (@INTER _112681 s t) = (term157 _112681 s t).
Proof. exact (EQ_MP (@lem4891586 _112681 s t) (@lem4892163 _112681 s t)). Qed.
Lemma lem4893931 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term157 A s t).
Proof. exact (@lem4893930 A s t). Qed.
Lemma lem4893932 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4893933 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term378 A P s t) = (term391 A P s t).
Proof. exact (MK_COMB (@lem4893932 A P) (@lem4893931 A s t)). Qed.
Lemma lem4893934 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term377 A s P t) = (term377 A s P t).
Proof. exact (eq_refl (term377 A s P t)). Qed.
Lemma lem4893935 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term380 A P s t) = (term392 A P s t).
Proof. exact (MK_COMB (@lem4893934 A s P t) (@lem4893933 A P s t)). Qed.
Lemma lem4893938 {A : Type'} (P : type686 A) (s : A -> Prop) : (term382 A P s) = (term393 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893935 A P s t)). Qed.
Lemma lem4893939 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893940 {A : Type'} (P : type686 A) (s : A -> Prop) : (term384 A P s) = (term394 A P s).
Proof. exact (MK_COMB (@lem4893939 A) (@lem4893938 A P s)). Qed.
Lemma lem4893945 {A : Type'} (P : type686 A) : (term386 A P) = (term395 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893940 A P s)). Qed.
Lemma lem4893946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893947 {A : Type'} (P : type686 A) : (term387 A P) = (term396 A P).
Proof. exact (MK_COMB (@lem4893946 A) (@lem4893945 A P)). Qed.
Lemma lem4893952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4893953 {A : Type'} (P : type686 A) : (term388 A P) = (term397 A P).
Proof. exact (MK_COMB (@lem4893952) (@lem4893947 A P)). Qed.
Lemma lem4893967 {_112681 : Type'} (s : _112681 -> Prop) (t : _112681 -> Prop) : (@INTER _112681 s t) = (term157 _112681 s t).
Proof. exact (EQ_MP (@lem4891586 _112681 s t) (@lem4892163 _112681 s t)). Qed.
Lemma lem4893968 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term157 A s t).
Proof. exact (@lem4893967 A s t). Qed.
Lemma lem4893969 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term230 A s t) = (term398 A s t).
Proof. exact (@lem4893968 A (@DIFF A (@UNIV A) s) (@DIFF A (@UNIV A) t)). Qed.
Lemma lem4893970 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4893971 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term324 A P s t) = (term399 A P s t).
Proof. exact (MK_COMB (@lem4893970 A P) (@lem4893969 A s t)). Qed.
Lemma lem4893972 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4893973 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term331 A P s t) = (term400 A P s t).
Proof. exact (MK_COMB (@lem4893972 A s P t) (@lem4893971 A P s t)). Qed.
Lemma lem4893976 {A : Type'} (P : type686 A) (s : A -> Prop) : (term332 A P s) = (term401 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4893973 A P s t)). Qed.
Lemma lem4893977 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893978 {A : Type'} (P : type686 A) (s : A -> Prop) : (term333 A P s) = (term402 A P s).
Proof. exact (MK_COMB (@lem4893977 A) (@lem4893976 A P s)). Qed.
Lemma lem4893983 {A : Type'} (P : type686 A) : (term334 A P) = (term403 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4893978 A P s)). Qed.
Lemma lem4893984 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4893985 {A : Type'} (P : type686 A) : (term335 A P) = (term404 A P).
Proof. exact (MK_COMB (@lem4893984 A) (@lem4893983 A P)). Qed.
Lemma lem4893990 {A : Type'} (P : type686 A) : ((term387 A P) = (term335 A P)) = ((term396 A P) = (term404 A P)).
Proof. exact (MK_COMB (@lem4893953 A P) (@lem4893985 A P)). Qed.
Lemma lem4893993 {A : Type'} : (term389 A) = (term405 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4893990 A P)). Qed.
Lemma lem4893994 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4893995 {A : Type'} : (term390 A) = (term406 A).
Proof. exact (MK_COMB (@lem4893994 A) (@lem4893993 A)). Qed.
Lemma lem4894000 {A : Type'} : (term406 A) = (term390 A).
Proof. exact (SYM (@lem4893995 A)). Qed.
Lemma lem4894028 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term4 _112654 P).
Proof. exact (EQ_MP (@lem4890906 _112654 P) (@lem4891560 _112654 P)). Qed.
Lemma lem4894029 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4894028 A P). Qed.
Lemma lem4894030 {A : Type'} (P : type686 A) : (term407 A P) = (term408 A P).
Proof. exact (@lem4894029 A (term409 A P)). Qed.
Lemma lem4894031 {A : Type'} (P : type686 A) (s : A -> Prop) : (term410 A P s) = (term394 A P s).
Proof. exact (eq_refl (term410 A P s)). Qed.
Lemma lem4894032 {A : Type'} (P : type686 A) : (term411 A P) = (term395 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894031 A P s)). Qed.
Lemma lem4894033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894034 {A : Type'} (P : type686 A) : (term407 A P) = (term396 A P).
Proof. exact (MK_COMB (@lem4894033 A) (@lem4894032 A P)). Qed.
Lemma lem4894035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4894036 {A : Type'} (P : type686 A) : (term412 A P) = (term397 A P).
Proof. exact (MK_COMB (@lem4894035) (@lem4894034 A P)). Qed.
Lemma lem4894037 {A : Type'} (P : type686 A) (s : A -> Prop) : (term413 A P s) = (term414 A P s).
Proof. exact (eq_refl (term413 A P s)). Qed.
Lemma lem4894038 {A : Type'} (P : type686 A) : (term415 A P) = (term409 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894037 A P s)). Qed.
Lemma lem4894039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894040 {A : Type'} (P : type686 A) : (term408 A P) = (term416 A P).
Proof. exact (MK_COMB (@lem4894039 A) (@lem4894038 A P)). Qed.
Lemma lem4894041 {A : Type'} (P : type686 A) : ((term407 A P) = (term408 A P)) = ((term396 A P) = (term416 A P)).
Proof. exact (MK_COMB (@lem4894036 A P) (@lem4894040 A P)). Qed.
Lemma lem4894042 {A : Type'} (P : type686 A) : (term396 A P) = (term416 A P).
Proof. exact (EQ_MP (@lem4894041 A P) (@lem4894030 A P)). Qed.
Lemma lem4894068 {_112654 : Type'} (P : type686 _112654) : (term3 _112654 P) = (term4 _112654 P).
Proof. exact (EQ_MP (@lem4890906 _112654 P) (@lem4891560 _112654 P)). Qed.
Lemma lem4894069 {A : Type'} (P : type686 A) : (term3 A P) = (term4 A P).
Proof. exact (@lem4894068 A P). Qed.
Lemma lem4894070 {A : Type'} (P : type686 A) (s : A -> Prop) : (term417 A P s) = (term418 A P s).
Proof. exact (@lem4894069 A (term312 A P s)). Qed.
Lemma lem4894071 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term419 A P s t) = (term420 A P s t).
Proof. exact (eq_refl (term419 A P s t)). Qed.
Lemma lem4894072 {A : Type'} (P : type686 A) (s : A -> Prop) : (term421 A P s) = (term422 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894071 A P s t)). Qed.
Lemma lem4894073 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894074 {A : Type'} (P : type686 A) (s : A -> Prop) : (term417 A P s) = (term414 A P s).
Proof. exact (MK_COMB (@lem4894073 A) (@lem4894072 A P s)). Qed.
Lemma lem4894075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4894076 {A : Type'} (P : type686 A) (s : A -> Prop) : (term423 A P s) = (term424 A P s).
Proof. exact (MK_COMB (@lem4894075) (@lem4894074 A P s)). Qed.
Lemma lem4894077 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term425 A P s t) = (term310 A P s t).
Proof. exact (eq_refl (term425 A P s t)). Qed.
Lemma lem4894078 {A : Type'} (P : type686 A) (s : A -> Prop) : (term426 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894077 A P s t)). Qed.
Lemma lem4894079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894080 {A : Type'} (P : type686 A) (s : A -> Prop) : (term418 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4894079 A) (@lem4894078 A P s)). Qed.
Lemma lem4894081 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term417 A P s) = (term418 A P s)) = ((term414 A P s) = (term314 A P s)).
Proof. exact (MK_COMB (@lem4894076 A P s) (@lem4894080 A P s)). Qed.
Lemma lem4894082 {A : Type'} (P : type686 A) (s : A -> Prop) : (term414 A P s) = (term314 A P s).
Proof. exact (EQ_MP (@lem4894081 A P s) (@lem4894070 A P s)). Qed.
Lemma lem4894107 {A : Type'} (P : type686 A) : (term409 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894082 A P s)). Qed.
Lemma lem4894108 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894109 {A : Type'} (P : type686 A) : (term416 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4894108 A) (@lem4894107 A P)). Qed.
Lemma lem4894130 {A : Type'} (P : type686 A) : (term396 A P) = (term318 A P).
Proof. exact (TRANS (@lem4894042 A P) (@lem4894109 A P)). Qed.
Lemma lem4894131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4894132 {A : Type'} (P : type686 A) : (term397 A P) = (term427 A P).
Proof. exact (MK_COMB (@lem4894131) (@lem4894130 A P)). Qed.
Lemma lem4894177 {A : Type'} (P : type686 A) : (term404 A P) = (term404 A P).
Proof. exact (eq_refl (term404 A P)). Qed.
Lemma lem4894178 {A : Type'} (P : type686 A) : ((term396 A P) = (term404 A P)) = ((term318 A P) = (term404 A P)).
Proof. exact (MK_COMB (@lem4894132 A P) (@lem4894177 A P)). Qed.
Lemma lem4894181 {A : Type'} : (term405 A) = (term428 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894178 A P)). Qed.
Lemma lem4894182 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894183 {A : Type'} : (term406 A) = (term429 A).
Proof. exact (MK_COMB (@lem4894182 A) (@lem4894181 A)). Qed.
Lemma lem4894204 {A : Type'} : (term429 A) = (term406 A).
Proof. exact (SYM (@lem4894183 A)). Qed.
Lemma lem4894236 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4890891 A s) (@lem4890890 A s)). Qed.
Lemma lem4894237 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4894236 A s). Qed.
Lemma lem4894238 {A : Type'} : (@UNION A) = (@UNION A).
Proof. exact (eq_refl (@UNION A)). Qed.
Lemma lem4894239 {A : Type'} (s : A -> Prop) : (term430 A s) = (@UNION A s).
Proof. exact (MK_COMB (@lem4894238 A) (@lem4894237 A s)). Qed.
Lemma lem4894241 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4890891 A s) (@lem4890890 A s)). Qed.
Lemma lem4894242 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4894241 A s). Qed.
Lemma lem4894243 {A : Type'} (t : A -> Prop) : (term1 A t) = t.
Proof. exact (@lem4894242 A t). Qed.
Lemma lem4894244 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term431 A s t) = (@UNION A s t).
Proof. exact (MK_COMB (@lem4894239 A s) (@lem4894243 A t)). Qed.
Lemma lem4894245 {A : Type'} : (@DIFF A (@UNIV A)) = (@DIFF A (@UNIV A)).
Proof. exact (eq_refl (@DIFF A (@UNIV A))). Qed.
Lemma lem4894246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term398 A s t) = (term229 A s t).
Proof. exact (MK_COMB (@lem4894245 A) (@lem4894244 A s t)). Qed.
Lemma lem4894247 {A : Type'} (P : type686 A) : (term323 A P) = (term323 A P).
Proof. exact (eq_refl (term323 A P)). Qed.
Lemma lem4894248 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term399 A P s t) = (term295 A P s t).
Proof. exact (MK_COMB (@lem4894247 A P) (@lem4894246 A s t)). Qed.
Lemma lem4894249 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term308 A s P t) = (term308 A s P t).
Proof. exact (eq_refl (term308 A s P t)). Qed.
Lemma lem4894250 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term400 A P s t) = (term310 A P s t).
Proof. exact (MK_COMB (@lem4894249 A s P t) (@lem4894248 A P s t)). Qed.
Lemma lem4894253 {A : Type'} (P : type686 A) (s : A -> Prop) : (term401 A P s) = (term312 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4894250 A P s t)). Qed.
Lemma lem4894254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894255 {A : Type'} (P : type686 A) (s : A -> Prop) : (term402 A P s) = (term314 A P s).
Proof. exact (MK_COMB (@lem4894254 A) (@lem4894253 A P s)). Qed.
Lemma lem4894260 {A : Type'} (P : type686 A) : (term403 A P) = (term316 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4894255 A P s)). Qed.
Lemma lem4894261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4894262 {A : Type'} (P : type686 A) : (term404 A P) = (term318 A P).
Proof. exact (MK_COMB (@lem4894261 A) (@lem4894260 A P)). Qed.
Lemma lem4894267 {A : Type'} (P : type686 A) : (term427 A P) = (term427 A P).
Proof. exact (eq_refl (term427 A P)). Qed.
Lemma lem4894268 {A : Type'} (P : type686 A) : ((term318 A P) = (term404 A P)) = ((term318 A P) = (term318 A P)).
Proof. exact (MK_COMB (@lem4894267 A P) (@lem4894262 A P)). Qed.
Lemma lem4894270 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4894271 (x : Prop) : (x = x) = True.
Proof. exact (@lem4894270 Prop x). Qed.
Lemma lem4894272 {A : Type'} (P : type686 A) : ((term318 A P) = (term318 A P)) = True.
Proof. exact (@lem4894271 (term318 A P)). Qed.
Lemma lem4894273 {A : Type'} (P : type686 A) : ((term318 A P) = (term404 A P)) = True.
Proof. exact (TRANS (@lem4894268 A P) (@lem4894272 A P)). Qed.
Lemma lem4894274 {A : Type'} : (term428 A) = (term432 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4894273 A P)). Qed.
Lemma lem4894275 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4894276 {A : Type'} : (term429 A) = (term433 A).
Proof. exact (MK_COMB (@lem4894275 A) (@lem4894274 A)). Qed.
Lemma lem4894278 {A : Type'} (t : Prop) : (term434 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4894279 {A : Type'} (t : Prop) : (term435 A t) = t.
Proof. exact (@lem4894278 (type686 A) t). Qed.
Lemma lem4894280 {A : Type'} : (term433 A) = True.
Proof. exact (@lem4894279 A True). Qed.
Lemma lem4894281 {A : Type'} : (term429 A) = True.
Proof. exact (TRANS (@lem4894276 A) (@lem4894280 A)). Qed.
Lemma lem4894282 {A : Type'} : True = (term429 A).
Proof. exact (SYM (@lem4894281 A)). Qed.
Lemma lem4894283 {A : Type'} : term429 A.
Proof. exact (EQ_MP (@lem4894282 A) (@lem0)). Qed.
Lemma lem4894284 {A : Type'} : term406 A.
Proof. exact (EQ_MP (@lem4894204 A) (@lem4894283 A)). Qed.
Lemma lem4894285 {A : Type'} : term390 A.
Proof. exact (EQ_MP (@lem4894000 A) (@lem4894284 A)). Qed.
Lemma lem4894286 {A : Type'} : term365 A.
Proof. exact (EQ_MP (@lem4893910 A) (@lem4894285 A)). Qed.
Lemma lem4894287 {A : Type'} : term337 A.
Proof. exact (EQ_MP (@lem4893810 A) (@lem4894286 A)). Qed.
Lemma lem4894288 {A : Type'} : term322 A.
Proof. exact (EQ_MP (@lem4893606 A) (@lem4894287 A)). Qed.
Lemma lem4894289 {A : Type'} : term321 A.
Proof. exact (EQ_MP (@lem4893517 A) (@lem4894288 A)). Qed.
