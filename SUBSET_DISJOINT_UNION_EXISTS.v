Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_DISJOINT_UNION_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import SUBSET_spec.
Require Import SUBSET_DISJOINT_UNION_spec.
Require Import disjoint_union_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm69_spec.
Lemma lem4469812 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term0 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4469813 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term0 _88435 _88436 P) = (term1 _88435 _88436 P).
Proof. exact (eq_refl (term0 _88435 _88436 P)). Qed.
Lemma lem4469814 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term1 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4469813 _88435 _88436 P) (@lem4469812 _88435 _88436 P)). Qed.
Lemma lem4469815 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term2 _88435 _88436 P a.
Proof. exact (@lem4469814 _88435 _88436 P a). Qed.
Lemma lem4469816 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term2 _88435 _88436 P a) = (term3 _88435 _88436 P a).
Proof. exact (eq_refl (term2 _88435 _88436 P a)). Qed.
Lemma lem4469817 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term3 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4469816 _88435 _88436 P a) (@lem4469815 _88435 _88436 P a)). Qed.
Lemma lem4469818 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term4 _88435 _88436 P a b.
Proof. exact (@lem4469817 _88435 _88436 P a b). Qed.
Lemma lem4469819 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term4 _88435 _88436 P a b) = ((term5 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term4 _88435 _88436 P a b)). Qed.
Lemma lem4469821 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term6 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4469822 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term6 _5106 _5107 P) = ((term7 _5106 _5107 P) = (term8 _5106 _5107 P)).
Proof. exact (eq_refl (term6 _5106 _5107 P)). Qed.
Lemma lem4469824 {A K : Type'} (k : K -> Prop) : term9 A K k.
Proof. exact (@lem4464464 A K k). Qed.
Lemma lem4469825 {A K : Type'} (k : K -> Prop) : (term9 A K k) = (term10 A K k).
Proof. exact (eq_refl (term9 A K k)). Qed.
Lemma lem4469826 {A K : Type'} (k : K -> Prop) : term10 A K k.
Proof. exact (EQ_MP (@lem4469825 A K k) (@lem4469824 A K k)). Qed.
Lemma lem4469827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term11 A K k s.
Proof. exact (@lem4469826 A K k s). Qed.
Lemma lem4469828 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term11 A K k s) = ((@disjoint_union A K k s) = (term12 A K k s)).
Proof. exact (eq_refl (term11 A K k s)). Qed.
Lemma lem4469830 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4469831 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4469832 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4469831 A s) (@lem4469830 A s)). Qed.
Lemma lem4469833 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4469832 A s t). Qed.
Lemma lem4469834 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((s = t) = (term16 A s t)).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4469836 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4469837 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4469838 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4469837 A s) (@lem4469836 A s)). Qed.
Lemma lem4469839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4469838 A s t). Qed.
Lemma lem4469840 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((@SUBSET A s t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4469852 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term21 A K u k s) : term21 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469854 (p : Prop) : p = (term22 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4469855 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term23 A K u k s) = (term24 A K u k s).
Proof. exact (@lem4469854 (term23 A K u k s)). Qed.
Lemma lem4469856 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term24 A K u k s) = (term23 A K u k s).
Proof. exact (SYM (@lem4469855 A K u k s)). Qed.
Lemma lem4469857 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term25 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469858 {A K : Type'} : term26 A K.
Proof. exact (@lem4466517 A K). Qed.
Lemma lem4469862 {A K : Type'} : term27 A K.
Proof. exact (@lem4466517 (prod K A) K). Qed.
Lemma lem4469865 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term28 A K u k s) : term28 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469866 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term29 A K u k s.
Proof. exact (fun h0 : term28 A K u k s => @lem4469865 A K u k s h0). Qed.
Lemma lem4469867 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term29 A K u k s) : term29 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469868 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term28 A K u k s) : term28 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469869 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term28 A K u k s) (h2 : term29 A K u k s) : term28 A K u k s.
Proof. exact (@lem4469867 A K u k s h2 (@lem4469868 A K u k s h1)). Qed.
Lemma lem4469870 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term28 A K u k s) : term30 A K u k s.
Proof. exact (fun h0 : term29 A K u k s => @lem4469869 A K u k s h1 h0). Qed.
Lemma lem4469871 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term29 A K u k s) : term29 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4469872 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term28 A K u k s) (h2 : term29 A K u k s) : term28 A K u k s.
Proof. exact (@lem4469870 A K u k s h1 (@lem4469871 A K u k s h2)). Qed.
Lemma lem4469873 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term29 A K u k s) : term29 A K u k s.
Proof. exact (fun h0 : term28 A K u k s => @lem4469872 A K u k s h0 h1). Qed.
Lemma lem4469874 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term31 A K u k s.
Proof. exact (fun h0 : term29 A K u k s => @lem4469873 A K u k s h0). Qed.
Lemma lem4469877 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term29 A K u k s.
Proof. exact (@lem4469874 A K u k s (@lem4469866 A K u k s)). Qed.
Lemma lem4469878 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term29 A K u k s.
Proof. exact (@lem4469877 A K u k s). Qed.
Lemma lem4469972 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4469973 {A K : Type'} : (term32 A K) = (term33 A K).
Proof. exact (@lem4469972 (term27 A K)). Qed.
Lemma lem4469992 {A K : Type'} : (term34 A K) = (term34 A K).
Proof. exact (eq_refl (term34 A K)). Qed.
Lemma lem4469993 {A K : Type'} : (term35 A K) = (term36 A K).
Proof. exact (MK_COMB (@lem4469992 A K) (@lem4469973 A K)). Qed.
Lemma lem4469996 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term37 A K u k s) = (term37 A K u k s).
Proof. exact (eq_refl (term37 A K u k s)). Qed.
Lemma lem4469997 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term28 A K u k s) = (term38 A K u k s).
Proof. exact (MK_COMB (@lem4469996 A K u k s) (@lem4469993 A K)). Qed.
Lemma lem4470000 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term39 A K k s) = (term40 A K k s).
Proof. exact (fun_ext (fun u : type1223 A K => @lem4469997 A K u k s)). Qed.
Lemma lem4470001 {A K : Type'} : (@all ((prod K A) -> Prop)) = (@all ((prod K A) -> Prop)).
Proof. exact (eq_refl (@all ((prod K A) -> Prop))). Qed.
Lemma lem4470002 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term41 A K k s) = (term42 A K k s).
Proof. exact (MK_COMB (@lem4470001 A K) (@lem4470000 A K k s)). Qed.
Lemma lem4470007 {A K : Type'} (s : type1470 A K) : (term43 A K s) = (term44 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470002 A K k s)). Qed.
Lemma lem4470008 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470009 {A K : Type'} (s : type1470 A K) : (term45 A K s) = (term46 A K s).
Proof. exact (MK_COMB (@lem4470008 K) (@lem4470007 A K s)). Qed.
Lemma lem4470014 {A K : Type'} : (term47 A K) = (term48 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470009 A K s)). Qed.
Lemma lem4470015 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470024 {A K : Type'} : (term49 A K) = (term50 A K).
Proof. exact (MK_COMB (@lem4470015 A K) (@lem4470014 A K)). Qed.
Lemma lem4470029 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term51 A K k s t i) = (term51 A K k s t i).
Proof. exact (eq_refl (term51 A K k s t i)). Qed.
Lemma lem4470030 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term52 A K k s t) = (term52 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4470029 A K k s t i)). Qed.
Lemma lem4470031 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4470032 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term53 A K k s t) = (term53 A K k s t).
Proof. exact (MK_COMB (@lem4470031 K) (@lem4470030 A K k s t)). Qed.
Lemma lem4470035 {A K : Type'} (s : type1462 A K) (k : K -> Prop) (t : type1462 A K) : (term54 A K s k t) = (term54 A K s k t).
Proof. exact (eq_refl (term54 A K s k t)). Qed.
Lemma lem4470036 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : ((term55 A K s k t) = (term53 A K k s t)) = ((term55 A K s k t) = (term53 A K k s t)).
Proof. exact (MK_COMB (@lem4470035 A K s k t) (@lem4470032 A K k s t)). Qed.
Lemma lem4470037 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term56 A K k s) = (term56 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4470036 A K k s t)). Qed.
Lemma lem4470038 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4470039 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term57 A K k s) = (term57 A K k s).
Proof. exact (MK_COMB (@lem4470038 A K) (@lem4470037 A K k s)). Qed.
Lemma lem4470040 {A K : Type'} (k : K -> Prop) : (term58 A K k) = (term58 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4470039 A K k s)). Qed.
Lemma lem4470041 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4470042 {A K : Type'} (k : K -> Prop) : (term59 A K k) = (term59 A K k).
Proof. exact (MK_COMB (@lem4470041 A K) (@lem4470040 A K k)). Qed.
Lemma lem4470043 {A K : Type'} : (term60 A K) = (term60 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470042 A K k)). Qed.
Lemma lem4470044 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470045 {A K : Type'} : (term27 A K) = (term27 A K).
Proof. exact (MK_COMB (@lem4470044 K) (@lem4470043 A K)). Qed.
Lemma lem4470046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4470047 {A K : Type'} : (term33 A K) = (term33 A K).
Proof. exact (MK_COMB (@lem4470046) (@lem4470045 A K)). Qed.
Lemma lem4470052 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term61 A K k s t i) = (term61 A K k s t i).
Proof. exact (eq_refl (term61 A K k s t i)). Qed.
Lemma lem4470053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term62 A K k s t) = (term62 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4470052 A K k s t i)). Qed.
Lemma lem4470054 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4470055 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term63 A K k s t) = (term63 A K k s t).
Proof. exact (MK_COMB (@lem4470054 K) (@lem4470053 A K k s t)). Qed.
Lemma lem4470058 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term64 A K s k t) = (term64 A K s k t).
Proof. exact (eq_refl (term64 A K s k t)). Qed.
Lemma lem4470059 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term65 A K s k t) = (term63 A K k s t)) = ((term65 A K s k t) = (term63 A K k s t)).
Proof. exact (MK_COMB (@lem4470058 A K s k t) (@lem4470055 A K k s t)). Qed.
Lemma lem4470060 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term66 A K k s) = (term66 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470059 A K k s t)). Qed.
Lemma lem4470061 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470062 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term67 A K k s) = (term67 A K k s).
Proof. exact (MK_COMB (@lem4470061 A K) (@lem4470060 A K k s)). Qed.
Lemma lem4470063 {A K : Type'} (k : K -> Prop) : (term68 A K k) = (term68 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470062 A K k s)). Qed.
Lemma lem4470064 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470065 {A K : Type'} (k : K -> Prop) : (term69 A K k) = (term69 A K k).
Proof. exact (MK_COMB (@lem4470064 A K) (@lem4470063 A K k)). Qed.
Lemma lem4470066 {A K : Type'} : (term70 A K) = (term70 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470065 A K k)). Qed.
Lemma lem4470067 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470068 {A K : Type'} : (term26 A K) = (term26 A K).
Proof. exact (MK_COMB (@lem4470067 K) (@lem4470066 A K)). Qed.
Lemma lem4470069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4470070 {A K : Type'} : (term34 A K) = (term34 A K).
Proof. exact (MK_COMB (@lem4470069) (@lem4470068 A K)). Qed.
Lemma lem4470071 {A K : Type'} : (term36 A K) = (term36 A K).
Proof. exact (MK_COMB (@lem4470070 A K) (@lem4470047 A K)). Qed.
Lemma lem4470072 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term21 A K u k s) = (term21 A K u k s).
Proof. exact (eq_refl (term21 A K u k s)). Qed.
Lemma lem4470077 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term61 A K k t s i) = (term61 A K k t s i).
Proof. exact (eq_refl (term61 A K k t s i)). Qed.
Lemma lem4470078 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term62 A K k t s) = (term62 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4470077 A K k t s i)). Qed.
Lemma lem4470079 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4470080 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term63 A K k t s) = (term63 A K k t s).
Proof. exact (MK_COMB (@lem4470079 K) (@lem4470078 A K k t s)). Qed.
Lemma lem4470083 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) : (term71 A K u k t) = (term71 A K u k t).
Proof. exact (eq_refl (term71 A K u k t)). Qed.
Lemma lem4470084 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term72 A K u k t s) = (term72 A K u k t s).
Proof. exact (MK_COMB (@lem4470083 A K u k t) (@lem4470080 A K k t s)). Qed.
Lemma lem4470085 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term73 A K u k s) = (term73 A K u k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470084 A K u k t s)). Qed.
Lemma lem4470086 {A K : Type'} : (@ex (K -> A -> Prop)) = (@ex (K -> A -> Prop)).
Proof. exact (eq_refl (@ex (K -> A -> Prop))). Qed.
Lemma lem4470087 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term74 A K u k s) = (term74 A K u k s).
Proof. exact (MK_COMB (@lem4470086 A K) (@lem4470085 A K u k s)). Qed.
Lemma lem4470088 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4470089 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term75 A K u k s) = (term75 A K u k s).
Proof. exact (MK_COMB (@lem4470088) (@lem4470087 A K u k s)). Qed.
Lemma lem4470090 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term23 A K u k s) = (term23 A K u k s).
Proof. exact (MK_COMB (@lem4470089 A K u k s) (@lem4470072 A K u k s)). Qed.
Lemma lem4470091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4470092 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term25 A K u k s) = (term25 A K u k s).
Proof. exact (MK_COMB (@lem4470091) (@lem4470090 A K u k s)). Qed.
Lemma lem4470093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4470094 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term37 A K u k s) = (term37 A K u k s).
Proof. exact (MK_COMB (@lem4470093) (@lem4470092 A K u k s)). Qed.
Lemma lem4470095 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term38 A K u k s) = (term38 A K u k s).
Proof. exact (MK_COMB (@lem4470094 A K u k s) (@lem4470071 A K)). Qed.
Lemma lem4470096 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term40 A K k s) = (term40 A K k s).
Proof. exact (fun_ext (fun u : type1223 A K => @lem4470095 A K u k s)). Qed.
Lemma lem4470097 {A K : Type'} : (@all ((prod K A) -> Prop)) = (@all ((prod K A) -> Prop)).
Proof. exact (eq_refl (@all ((prod K A) -> Prop))). Qed.
Lemma lem4470098 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term42 A K k s) = (term42 A K k s).
Proof. exact (MK_COMB (@lem4470097 A K) (@lem4470096 A K k s)). Qed.
Lemma lem4470099 {A K : Type'} (s : type1470 A K) : (term44 A K s) = (term44 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470098 A K k s)). Qed.
Lemma lem4470100 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470101 {A K : Type'} (s : type1470 A K) : (term46 A K s) = (term46 A K s).
Proof. exact (MK_COMB (@lem4470100 K) (@lem4470099 A K s)). Qed.
Lemma lem4470102 {A K : Type'} : (term48 A K) = (term48 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470101 A K s)). Qed.
Lemma lem4470103 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470104 {A K : Type'} : (term50 A K) = (term50 A K).
Proof. exact (MK_COMB (@lem4470103 A K) (@lem4470102 A K)). Qed.
Lemma lem4470199 {A K : Type'} : (term49 A K) = (term50 A K).
Proof. exact (TRANS (@lem4470024 A K) (@lem4470104 A K)). Qed.
Lemma lem4470200 {A K : Type'} : (term50 A K) = (term49 A K).
Proof. exact (SYM (@lem4470199 A K)). Qed.
Lemma lem4470201 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term25 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4470202 {A K : Type'} (h1 : term26 A K) : term26 A K.
Proof. exact (h1). Qed.
Lemma lem4470203 {A K : Type'} (h1 : term27 A K) : term27 A K.
Proof. exact (h1). Qed.
Lemma lem4470211 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term61 A K k t s i) = (term76 A K k t s i).
Proof. exact (@lem17265 (@IN K i k) (term77 A K t s i)). Qed.
Lemma lem4470212 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term62 A K k t s) = (term78 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4470211 A K k t s i)). Qed.
Lemma lem4470213 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4470214 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term63 A K k t s) = (term79 A K k t s).
Proof. exact (MK_COMB (@lem4470213 K) (@lem4470212 A K k t s)). Qed.
Lemma lem4470216 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) : (term71 A K u k t) = (term71 A K u k t).
Proof. exact (eq_refl (term71 A K u k t)). Qed.
Lemma lem4470217 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term72 A K u k t s) = (term80 A K u k t s).
Proof. exact (MK_COMB (@lem4470216 A K u k t) (@lem4470214 A K k t s)). Qed.
Lemma lem4470218 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term73 A K u k s) = (term81 A K u k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470217 A K u k t s)). Qed.
Lemma lem4470219 {A K : Type'} : (@ex (K -> A -> Prop)) = (@ex (K -> A -> Prop)).
Proof. exact (eq_refl (@ex (K -> A -> Prop))). Qed.
Lemma lem4470220 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term74 A K u k s) = (term82 A K u k s).
Proof. exact (MK_COMB (@lem4470219 A K) (@lem4470218 A K u k s)). Qed.
Lemma lem4470221 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term83 A K u k s) = (term83 A K u k s).
Proof. exact (eq_refl (term83 A K u k s)). Qed.
Lemma lem4470222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470223 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term84 A K u k s) = (term85 A K u k s).
Proof. exact (MK_COMB (@lem4470222) (@lem4470220 A K u k s)). Qed.
Lemma lem4470224 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term86 A K u k s) = (term87 A K u k s).
Proof. exact (MK_COMB (@lem4470223 A K u k s) (@lem4470221 A K u k s)). Qed.
Lemma lem4470225 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term25 A K u k s) = (term86 A K u k s).
Proof. exact (@lem17362 (term74 A K u k s) (term21 A K u k s)). Qed.
Lemma lem4470226 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term25 A K u k s) = (term87 A K u k s).
Proof. exact (TRANS (@lem4470225 A K u k s) (@lem4470224 A K u k s)). Qed.
Lemma lem4470325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4470326 {A K : Type'} (P : type745 A K) (Q : Prop) : (term90 A K P Q) = (term91 A K P Q).
Proof. exact (@lem4470325 (type1470 A K) P Q). Qed.
Lemma lem4470327 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term92 A K u k s) = (term93 A K u k s).
Proof. exact (@lem4470326 A K (term81 A K u k s) (term83 A K u k s)). Qed.
Lemma lem4470328 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term94 A K u k s t) = (term80 A K u k t s).
Proof. exact (eq_refl (term94 A K u k s t)). Qed.
Lemma lem4470329 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term95 A K u k s) = (term81 A K u k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470328 A K u k t s)). Qed.
Lemma lem4470330 {A K : Type'} : (@ex (K -> A -> Prop)) = (@ex (K -> A -> Prop)).
Proof. exact (eq_refl (@ex (K -> A -> Prop))). Qed.
Lemma lem4470331 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term96 A K u k s) = (term82 A K u k s).
Proof. exact (MK_COMB (@lem4470330 A K) (@lem4470329 A K u k s)). Qed.
Lemma lem4470332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470333 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term97 A K u k s) = (term85 A K u k s).
Proof. exact (MK_COMB (@lem4470332) (@lem4470331 A K u k s)). Qed.
Lemma lem4470334 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term83 A K u k s) = (term83 A K u k s).
Proof. exact (eq_refl (term83 A K u k s)). Qed.
Lemma lem4470335 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term92 A K u k s) = (term87 A K u k s).
Proof. exact (MK_COMB (@lem4470333 A K u k s) (@lem4470334 A K u k s)). Qed.
Lemma lem4470336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4470337 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term98 A K u k s) = (term99 A K u k s).
Proof. exact (MK_COMB (@lem4470336) (@lem4470335 A K u k s)). Qed.
Lemma lem4470338 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term94 A K u k s t) = (term80 A K u k t s).
Proof. exact (eq_refl (term94 A K u k s t)). Qed.
Lemma lem4470339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470340 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term100 A K u k s t) = (term101 A K u k t s).
Proof. exact (MK_COMB (@lem4470339) (@lem4470338 A K u k t s)). Qed.
Lemma lem4470341 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term83 A K u k s) = (term83 A K u k s).
Proof. exact (eq_refl (term83 A K u k s)). Qed.
Lemma lem4470342 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term102 A K t u k s) = (term103 A K t u k s).
Proof. exact (MK_COMB (@lem4470340 A K u k t s) (@lem4470341 A K u k s)). Qed.
Lemma lem4470343 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term104 A K u k s) = (term105 A K u k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470342 A K t u k s)). Qed.
Lemma lem4470344 {A K : Type'} : (@ex (K -> A -> Prop)) = (@ex (K -> A -> Prop)).
Proof. exact (eq_refl (@ex (K -> A -> Prop))). Qed.
Lemma lem4470345 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term93 A K u k s) = (term106 A K u k s).
Proof. exact (MK_COMB (@lem4470344 A K) (@lem4470343 A K u k s)). Qed.
Lemma lem4470346 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : ((term92 A K u k s) = (term93 A K u k s)) = ((term87 A K u k s) = (term106 A K u k s)).
Proof. exact (MK_COMB (@lem4470337 A K u k s) (@lem4470345 A K u k s)). Qed.
Lemma lem4470348 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term87 A K u k s) = (term106 A K u k s).
Proof. exact (EQ_MP (@lem4470346 A K u k s) (@lem4470327 A K u k s)). Qed.
Lemma lem4470349 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term25 A K u k s) = (term106 A K u k s).
Proof. exact (TRANS (@lem4470226 A K u k s) (@lem4470348 A K u k s)). Qed.
Lemma lem4470350 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term106 A K u k s.
Proof. exact (EQ_MP (@lem4470349 A K u k s) (@lem4470201 A K u k s h1)). Qed.
Lemma lem4470361 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term107 A K k s t i) = (term108 A K k s t i).
Proof. exact (@lem17362 (@IN K i k) (term77 A K s t i)). Qed.
Lemma lem4470366 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term61 A K k s t i) = (term76 A K k s t i).
Proof. exact (@lem17265 (@IN K i k) (term77 A K s t i)). Qed.
Lemma lem4470367 {K : Type'} (P : K -> Prop) : (term109 K P) = (term110 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4470368 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term111 A K k s t) = (term112 A K k s t).
Proof. exact (@lem4470367 K (term62 A K k s t)). Qed.
Lemma lem4470369 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term113 A K k s t i) = (term61 A K k s t i).
Proof. exact (eq_refl (term113 A K k s t i)). Qed.
Lemma lem4470370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4470371 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term114 A K k s t i) = (term107 A K k s t i).
Proof. exact (MK_COMB (@lem4470370) (@lem4470369 A K k s t i)). Qed.
Lemma lem4470372 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term114 A K k s t i) = (term108 A K k s t i).
Proof. exact (TRANS (@lem4470371 A K k s t i) (@lem4470361 A K k s t i)). Qed.
Lemma lem4470373 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term115 A K k s t) = (term116 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4470372 A K k s t i)). Qed.
Lemma lem4470374 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4470375 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term112 A K k s t) = (term117 A K k s t).
Proof. exact (MK_COMB (@lem4470374 K) (@lem4470373 A K k s t)). Qed.
Lemma lem4470376 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term111 A K k s t) = (term117 A K k s t).
Proof. exact (TRANS (@lem4470368 A K k s t) (@lem4470375 A K k s t)). Qed.
Lemma lem4470377 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term62 A K k s t) = (term78 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4470366 A K k s t i)). Qed.
Lemma lem4470378 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4470379 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term63 A K k s t) = (term79 A K k s t).
Proof. exact (MK_COMB (@lem4470378 K) (@lem4470377 A K k s t)). Qed.
Lemma lem4470381 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term118 A K s k t) = (term118 A K s k t).
Proof. exact (eq_refl (term118 A K s k t)). Qed.
Lemma lem4470382 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term119 A K k s t) = (term120 A K k s t).
Proof. exact (MK_COMB (@lem4470381 A K s k t) (@lem4470379 A K k s t)). Qed.
Lemma lem4470384 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term121 A K s k t) = (term121 A K s k t).
Proof. exact (eq_refl (term121 A K s k t)). Qed.
Lemma lem4470385 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term122 A K k s t) = (term123 A K k s t).
Proof. exact (MK_COMB (@lem4470384 A K s k t) (@lem4470376 A K k s t)). Qed.
Lemma lem4470386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470387 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term124 A K k s t) = (term125 A K k s t).
Proof. exact (MK_COMB (@lem4470386) (@lem4470385 A K k s t)). Qed.
Lemma lem4470388 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term126 A K k s t) = (term127 A K k s t).
Proof. exact (MK_COMB (@lem4470387 A K k s t) (@lem4470382 A K k s t)). Qed.
Lemma lem4470389 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term65 A K s k t) = (term63 A K k s t)) = (term126 A K k s t).
Proof. exact (@lem17784 (term65 A K s k t) (term63 A K k s t)). Qed.
Lemma lem4470390 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term65 A K s k t) = (term63 A K k s t)) = (term127 A K k s t).
Proof. exact (TRANS (@lem4470389 A K k s t) (@lem4470388 A K k s t)). Qed.
Lemma lem4470391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term66 A K k s) = (term128 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470390 A K k s t)). Qed.
Lemma lem4470392 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470393 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term67 A K k s) = (term129 A K k s).
Proof. exact (MK_COMB (@lem4470392 A K) (@lem4470391 A K k s)). Qed.
Lemma lem4470394 {A K : Type'} (k : K -> Prop) : (term68 A K k) = (term130 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470393 A K k s)). Qed.
Lemma lem4470395 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470396 {A K : Type'} (k : K -> Prop) : (term69 A K k) = (term131 A K k).
Proof. exact (MK_COMB (@lem4470395 A K) (@lem4470394 A K k)). Qed.
Lemma lem4470397 {A K : Type'} : (term70 A K) = (term132 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470396 A K k)). Qed.
Lemma lem4470398 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470399 {A K : Type'} : (term26 A K) = (term133 A K).
Proof. exact (MK_COMB (@lem4470398 K) (@lem4470397 A K)). Qed.
Lemma lem4470409 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4470410 {A K : Type'} (P : type745 A K) (Q : type745 A K) : (term136 A K P Q) = (term137 A K P Q).
Proof. exact (@lem4470409 (type1470 A K) P Q). Qed.
Lemma lem4470411 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term138 A K k s) = (term139 A K k s).
Proof. exact (@lem4470410 A K (term140 A K k s) (term141 A K k s)). Qed.
Lemma lem4470412 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term142 A K k s t) = (term123 A K k s t).
Proof. exact (eq_refl (term142 A K k s t)). Qed.
Lemma lem4470413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470414 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term143 A K k s t) = (term125 A K k s t).
Proof. exact (MK_COMB (@lem4470413) (@lem4470412 A K k s t)). Qed.
Lemma lem4470415 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term144 A K k s t) = (term120 A K k s t).
Proof. exact (eq_refl (term144 A K k s t)). Qed.
Lemma lem4470416 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term145 A K k s t) = (term127 A K k s t).
Proof. exact (MK_COMB (@lem4470414 A K k s t) (@lem4470415 A K k s t)). Qed.
Lemma lem4470417 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term146 A K k s) = (term128 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470416 A K k s t)). Qed.
Lemma lem4470418 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470419 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term138 A K k s) = (term129 A K k s).
Proof. exact (MK_COMB (@lem4470418 A K) (@lem4470417 A K k s)). Qed.
Lemma lem4470420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4470421 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4470420) (@lem4470419 A K k s)). Qed.
Lemma lem4470422 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term142 A K k s t) = (term123 A K k s t).
Proof. exact (eq_refl (term142 A K k s t)). Qed.
Lemma lem4470423 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term149 A K k s) = (term140 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470422 A K k s t)). Qed.
Lemma lem4470424 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470425 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term150 A K k s) = (term151 A K k s).
Proof. exact (MK_COMB (@lem4470424 A K) (@lem4470423 A K k s)). Qed.
Lemma lem4470426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470427 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term152 A K k s) = (term153 A K k s).
Proof. exact (MK_COMB (@lem4470426) (@lem4470425 A K k s)). Qed.
Lemma lem4470428 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term144 A K k s t) = (term120 A K k s t).
Proof. exact (eq_refl (term144 A K k s t)). Qed.
Lemma lem4470429 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term154 A K k s) = (term141 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4470428 A K k s t)). Qed.
Lemma lem4470430 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term155 A K k s) = (term156 A K k s).
Proof. exact (MK_COMB (@lem4470430 A K) (@lem4470429 A K k s)). Qed.
Lemma lem4470432 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term139 A K k s) = (term157 A K k s).
Proof. exact (MK_COMB (@lem4470427 A K k s) (@lem4470431 A K k s)). Qed.
Lemma lem4470433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term138 A K k s) = (term139 A K k s)) = ((term129 A K k s) = (term157 A K k s)).
Proof. exact (MK_COMB (@lem4470421 A K k s) (@lem4470432 A K k s)). Qed.
Lemma lem4470434 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term129 A K k s) = (term157 A K k s).
Proof. exact (EQ_MP (@lem4470433 A K k s) (@lem4470411 A K k s)). Qed.
Lemma lem4470627 {A K : Type'} (k : K -> Prop) : (term130 A K k) = (term158 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470434 A K k s)). Qed.
Lemma lem4470628 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470629 {A K : Type'} (k : K -> Prop) : (term131 A K k) = (term159 A K k).
Proof. exact (MK_COMB (@lem4470628 A K) (@lem4470627 A K k)). Qed.
Lemma lem4470631 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4470632 {A K : Type'} (P : type745 A K) (Q : type745 A K) : (term136 A K P Q) = (term137 A K P Q).
Proof. exact (@lem4470631 (type1470 A K) P Q). Qed.
Lemma lem4470633 {A K : Type'} (k : K -> Prop) : (term160 A K k) = (term161 A K k).
Proof. exact (@lem4470632 A K (term162 A K k) (term163 A K k)). Qed.
Lemma lem4470634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term164 A K k s) = (term151 A K k s).
Proof. exact (eq_refl (term164 A K k s)). Qed.
Lemma lem4470635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470636 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term165 A K k s) = (term153 A K k s).
Proof. exact (MK_COMB (@lem4470635) (@lem4470634 A K k s)). Qed.
Lemma lem4470637 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term166 A K k s) = (term156 A K k s).
Proof. exact (eq_refl (term166 A K k s)). Qed.
Lemma lem4470638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term167 A K k s) = (term157 A K k s).
Proof. exact (MK_COMB (@lem4470636 A K k s) (@lem4470637 A K k s)). Qed.
Lemma lem4470639 {A K : Type'} (k : K -> Prop) : (term168 A K k) = (term158 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470638 A K k s)). Qed.
Lemma lem4470640 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470641 {A K : Type'} (k : K -> Prop) : (term160 A K k) = (term159 A K k).
Proof. exact (MK_COMB (@lem4470640 A K) (@lem4470639 A K k)). Qed.
Lemma lem4470642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4470643 {A K : Type'} (k : K -> Prop) : (term169 A K k) = (term170 A K k).
Proof. exact (MK_COMB (@lem4470642) (@lem4470641 A K k)). Qed.
Lemma lem4470644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term164 A K k s) = (term151 A K k s).
Proof. exact (eq_refl (term164 A K k s)). Qed.
Lemma lem4470645 {A K : Type'} (k : K -> Prop) : (term171 A K k) = (term162 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470644 A K k s)). Qed.
Lemma lem4470646 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470647 {A K : Type'} (k : K -> Prop) : (term172 A K k) = (term173 A K k).
Proof. exact (MK_COMB (@lem4470646 A K) (@lem4470645 A K k)). Qed.
Lemma lem4470648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470649 {A K : Type'} (k : K -> Prop) : (term174 A K k) = (term175 A K k).
Proof. exact (MK_COMB (@lem4470648) (@lem4470647 A K k)). Qed.
Lemma lem4470650 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term166 A K k s) = (term156 A K k s).
Proof. exact (eq_refl (term166 A K k s)). Qed.
Lemma lem4470651 {A K : Type'} (k : K -> Prop) : (term176 A K k) = (term163 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4470650 A K k s)). Qed.
Lemma lem4470652 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4470653 {A K : Type'} (k : K -> Prop) : (term177 A K k) = (term178 A K k).
Proof. exact (MK_COMB (@lem4470652 A K) (@lem4470651 A K k)). Qed.
Lemma lem4470654 {A K : Type'} (k : K -> Prop) : (term161 A K k) = (term179 A K k).
Proof. exact (MK_COMB (@lem4470649 A K k) (@lem4470653 A K k)). Qed.
Lemma lem4470655 {A K : Type'} (k : K -> Prop) : ((term160 A K k) = (term161 A K k)) = ((term159 A K k) = (term179 A K k)).
Proof. exact (MK_COMB (@lem4470643 A K k) (@lem4470654 A K k)). Qed.
Lemma lem4470656 {A K : Type'} (k : K -> Prop) : (term159 A K k) = (term179 A K k).
Proof. exact (EQ_MP (@lem4470655 A K k) (@lem4470633 A K k)). Qed.
Lemma lem4470857 {A K : Type'} (k : K -> Prop) : (term131 A K k) = (term179 A K k).
Proof. exact (TRANS (@lem4470629 A K k) (@lem4470656 A K k)). Qed.
Lemma lem4470858 {A K : Type'} : (term132 A K) = (term180 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470857 A K k)). Qed.
Lemma lem4470859 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470860 {A K : Type'} : (term133 A K) = (term181 A K).
Proof. exact (MK_COMB (@lem4470859 K) (@lem4470858 A K)). Qed.
Lemma lem4470862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4470863 {K : Type'} (P : type686 K) (Q : type686 K) : (term182 K P Q) = (term183 K P Q).
Proof. exact (@lem4470862 (K -> Prop) P Q). Qed.
Lemma lem4470864 {A K : Type'} : (term184 A K) = (term185 A K).
Proof. exact (@lem4470863 K (term186 A K) (term187 A K)). Qed.
Lemma lem4470865 {A K : Type'} (k : K -> Prop) : (term188 A K k) = (term173 A K k).
Proof. exact (eq_refl (term188 A K k)). Qed.
Lemma lem4470866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470867 {A K : Type'} (k : K -> Prop) : (term189 A K k) = (term175 A K k).
Proof. exact (MK_COMB (@lem4470866) (@lem4470865 A K k)). Qed.
Lemma lem4470868 {A K : Type'} (k : K -> Prop) : (term190 A K k) = (term178 A K k).
Proof. exact (eq_refl (term190 A K k)). Qed.
Lemma lem4470869 {A K : Type'} (k : K -> Prop) : (term191 A K k) = (term179 A K k).
Proof. exact (MK_COMB (@lem4470867 A K k) (@lem4470868 A K k)). Qed.
Lemma lem4470870 {A K : Type'} : (term192 A K) = (term180 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470869 A K k)). Qed.
Lemma lem4470871 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470872 {A K : Type'} : (term184 A K) = (term181 A K).
Proof. exact (MK_COMB (@lem4470871 K) (@lem4470870 A K)). Qed.
Lemma lem4470873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4470874 {A K : Type'} : (term193 A K) = (term194 A K).
Proof. exact (MK_COMB (@lem4470873) (@lem4470872 A K)). Qed.
Lemma lem4470875 {A K : Type'} (k : K -> Prop) : (term188 A K k) = (term173 A K k).
Proof. exact (eq_refl (term188 A K k)). Qed.
Lemma lem4470876 {A K : Type'} : (term195 A K) = (term186 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470875 A K k)). Qed.
Lemma lem4470877 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470878 {A K : Type'} : (term196 A K) = (term197 A K).
Proof. exact (MK_COMB (@lem4470877 K) (@lem4470876 A K)). Qed.
Lemma lem4470879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4470880 {A K : Type'} : (term198 A K) = (term199 A K).
Proof. exact (MK_COMB (@lem4470879) (@lem4470878 A K)). Qed.
Lemma lem4470881 {A K : Type'} (k : K -> Prop) : (term190 A K k) = (term178 A K k).
Proof. exact (eq_refl (term190 A K k)). Qed.
Lemma lem4470882 {A K : Type'} : (term200 A K) = (term187 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4470881 A K k)). Qed.
Lemma lem4470883 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4470884 {A K : Type'} : (term201 A K) = (term202 A K).
Proof. exact (MK_COMB (@lem4470883 K) (@lem4470882 A K)). Qed.
Lemma lem4470885 {A K : Type'} : (term185 A K) = (term203 A K).
Proof. exact (MK_COMB (@lem4470880 A K) (@lem4470884 A K)). Qed.
Lemma lem4470886 {A K : Type'} : ((term184 A K) = (term185 A K)) = ((term181 A K) = (term203 A K)).
Proof. exact (MK_COMB (@lem4470874 A K) (@lem4470885 A K)). Qed.
Lemma lem4470887 {A K : Type'} : (term181 A K) = (term203 A K).
Proof. exact (EQ_MP (@lem4470886 A K) (@lem4470864 A K)). Qed.
Lemma lem4471096 {A K : Type'} : (term133 A K) = (term203 A K).
Proof. exact (TRANS (@lem4470860 A K) (@lem4470887 A K)). Qed.
Lemma lem4471098 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4471099 {K : Type'} (P : Prop) (Q : K -> Prop) : (term204 K P Q) = (term205 K P Q).
Proof. exact (@lem4471098 K P Q). Qed.
Lemma lem4471100 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term206 A K k s t) = (term207 A K k s t).
Proof. exact (@lem4471099 K (term65 A K s k t) (term116 A K k s t)). Qed.
Lemma lem4471101 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term208 A K k s t i) = (term108 A K k s t i).
Proof. exact (eq_refl (term208 A K k s t i)). Qed.
Lemma lem4471102 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term209 A K k s t) = (term116 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4471101 A K k s t i)). Qed.
Lemma lem4471103 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4471104 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term210 A K k s t) = (term117 A K k s t).
Proof. exact (MK_COMB (@lem4471103 K) (@lem4471102 A K k s t)). Qed.
Lemma lem4471105 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term121 A K s k t) = (term121 A K s k t).
Proof. exact (eq_refl (term121 A K s k t)). Qed.
Lemma lem4471106 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term206 A K k s t) = (term123 A K k s t).
Proof. exact (MK_COMB (@lem4471105 A K s k t) (@lem4471104 A K k s t)). Qed.
Lemma lem4471107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471108 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term211 A K k s t) = (term212 A K k s t).
Proof. exact (MK_COMB (@lem4471107) (@lem4471106 A K k s t)). Qed.
Lemma lem4471109 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term208 A K k s t i) = (term108 A K k s t i).
Proof. exact (eq_refl (term208 A K k s t i)). Qed.
Lemma lem4471110 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term121 A K s k t) = (term121 A K s k t).
Proof. exact (eq_refl (term121 A K s k t)). Qed.
Lemma lem4471111 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term213 A K k s t i) = (term214 A K k s t i).
Proof. exact (MK_COMB (@lem4471110 A K s k t) (@lem4471109 A K k s t i)). Qed.
Lemma lem4471112 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term215 A K k s t) = (term216 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4471111 A K k s t i)). Qed.
Lemma lem4471113 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4471114 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term207 A K k s t) = (term217 A K k s t).
Proof. exact (MK_COMB (@lem4471113 K) (@lem4471112 A K k s t)). Qed.
Lemma lem4471115 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term206 A K k s t) = (term207 A K k s t)) = ((term123 A K k s t) = (term217 A K k s t)).
Proof. exact (MK_COMB (@lem4471108 A K k s t) (@lem4471114 A K k s t)). Qed.
Lemma lem4471116 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term123 A K k s t) = (term217 A K k s t).
Proof. exact (EQ_MP (@lem4471115 A K k s t) (@lem4471100 A K k s t)). Qed.
Lemma lem4471117 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term140 A K k s) = (term218 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4471116 A K k s t)). Qed.
Lemma lem4471118 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471119 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term151 A K k s) = (term219 A K k s).
Proof. exact (MK_COMB (@lem4471118 A K) (@lem4471117 A K k s)). Qed.
Lemma lem4471121 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4471122 {A K : Type'} (P : type742 A K) : (term222 A K P) = (term223 A K P).
Proof. exact (@lem4471121 (type1470 A K) K P). Qed.
Lemma lem4471123 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term224 A K k s) = (term225 A K k s).
Proof. exact (@lem4471122 A K (term226 A K k s)). Qed.
Lemma lem4471124 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term227 A K k s t) = (term216 A K k s t).
Proof. exact (eq_refl (term227 A K k s t)). Qed.
Lemma lem4471125 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4471126 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term228 A K k s t i) = (term229 A K k s t i).
Proof. exact (MK_COMB (@lem4471124 A K k s t) (@lem4471125 K i)). Qed.
Lemma lem4471127 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term229 A K k s t i) = (term214 A K k s t i).
Proof. exact (eq_refl (term229 A K k s t i)). Qed.
Lemma lem4471128 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term228 A K k s t i) = (term214 A K k s t i).
Proof. exact (TRANS (@lem4471126 A K k s t i) (@lem4471127 A K k s t i)). Qed.
Lemma lem4471129 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term230 A K k s t) = (term216 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4471128 A K k s t i)). Qed.
Lemma lem4471130 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4471131 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term231 A K k s t) = (term217 A K k s t).
Proof. exact (MK_COMB (@lem4471130 K) (@lem4471129 A K k s t)). Qed.
Lemma lem4471132 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term232 A K k s) = (term218 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4471131 A K k s t)). Qed.
Lemma lem4471133 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471134 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term224 A K k s) = (term219 A K k s).
Proof. exact (MK_COMB (@lem4471133 A K) (@lem4471132 A K k s)). Qed.
Lemma lem4471135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471136 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term233 A K k s) = (term234 A K k s).
Proof. exact (MK_COMB (@lem4471135) (@lem4471134 A K k s)). Qed.
Lemma lem4471137 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term227 A K k s t) = (term216 A K k s t).
Proof. exact (eq_refl (term227 A K k s t)). Qed.
Lemma lem4471138 {A K : Type'} (i : type744 A K) (t : type1470 A K) : (i t) = (i t).
Proof. exact (eq_refl (i t)). Qed.
Lemma lem4471139 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) (t : type1470 A K) : (term235 A K k s i t) = (term236 A K k s i t).
Proof. exact (MK_COMB (@lem4471137 A K k s t) (@lem4471138 A K i t)). Qed.
Lemma lem4471140 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) (t : type1470 A K) : (term236 A K k s i t) = (term237 A K k s i t).
Proof. exact (eq_refl (term236 A K k s i t)). Qed.
Lemma lem4471141 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) (t : type1470 A K) : (term235 A K k s i t) = (term237 A K k s i t).
Proof. exact (TRANS (@lem4471139 A K k s i t) (@lem4471140 A K k s i t)). Qed.
Lemma lem4471142 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) : (term238 A K k s i) = (term239 A K k s i).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4471141 A K k s i t)). Qed.
Lemma lem4471143 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471144 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) : (term240 A K k s i) = (term241 A K k s i).
Proof. exact (MK_COMB (@lem4471143 A K) (@lem4471142 A K k s i)). Qed.
Lemma lem4471145 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term242 A K k s) = (term243 A K k s).
Proof. exact (fun_ext (fun i : type744 A K => @lem4471144 A K k s i)). Qed.
Lemma lem4471146 {A K : Type'} : (@ex ((K -> A -> Prop) -> K)) = (@ex ((K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> A -> Prop) -> K))). Qed.
Lemma lem4471147 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term225 A K k s) = (term244 A K k s).
Proof. exact (MK_COMB (@lem4471146 A K) (@lem4471145 A K k s)). Qed.
Lemma lem4471148 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term224 A K k s) = (term225 A K k s)) = ((term219 A K k s) = (term244 A K k s)).
Proof. exact (MK_COMB (@lem4471136 A K k s) (@lem4471147 A K k s)). Qed.
Lemma lem4471149 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term219 A K k s) = (term244 A K k s).
Proof. exact (EQ_MP (@lem4471148 A K k s) (@lem4471123 A K k s)). Qed.
Lemma lem4471150 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term151 A K k s) = (term244 A K k s).
Proof. exact (TRANS (@lem4471119 A K k s) (@lem4471149 A K k s)). Qed.
Lemma lem4471151 {A K : Type'} (k : K -> Prop) : (term162 A K k) = (term245 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4471150 A K k s)). Qed.
Lemma lem4471152 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471153 {A K : Type'} (k : K -> Prop) : (term173 A K k) = (term246 A K k).
Proof. exact (MK_COMB (@lem4471152 A K) (@lem4471151 A K k)). Qed.
Lemma lem4471155 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4471156 {A K : Type'} (P : type728 A K) : (term247 A K P) = (term248 A K P).
Proof. exact (@lem4471155 (type1470 A K) (type744 A K) P). Qed.
Lemma lem4471157 {A K : Type'} (k : K -> Prop) : (term249 A K k) = (term250 A K k).
Proof. exact (@lem4471156 A K (term251 A K k)). Qed.
Lemma lem4471158 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term252 A K k s) = (term243 A K k s).
Proof. exact (eq_refl (term252 A K k s)). Qed.
Lemma lem4471159 {A K : Type'} (i : type744 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4471160 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) : (term253 A K k s i) = (term254 A K k s i).
Proof. exact (MK_COMB (@lem4471158 A K k s) (@lem4471159 A K i)). Qed.
Lemma lem4471161 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) : (term254 A K k s i) = (term241 A K k s i).
Proof. exact (eq_refl (term254 A K k s i)). Qed.
Lemma lem4471162 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type744 A K) : (term253 A K k s i) = (term241 A K k s i).
Proof. exact (TRANS (@lem4471160 A K k s i) (@lem4471161 A K k s i)). Qed.
Lemma lem4471163 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term255 A K k s) = (term243 A K k s).
Proof. exact (fun_ext (fun i : type744 A K => @lem4471162 A K k s i)). Qed.
Lemma lem4471164 {A K : Type'} : (@ex ((K -> A -> Prop) -> K)) = (@ex ((K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> A -> Prop) -> K))). Qed.
Lemma lem4471165 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term256 A K k s) = (term244 A K k s).
Proof. exact (MK_COMB (@lem4471164 A K) (@lem4471163 A K k s)). Qed.
Lemma lem4471166 {A K : Type'} (k : K -> Prop) : (term257 A K k) = (term245 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4471165 A K k s)). Qed.
Lemma lem4471167 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471168 {A K : Type'} (k : K -> Prop) : (term249 A K k) = (term246 A K k).
Proof. exact (MK_COMB (@lem4471167 A K) (@lem4471166 A K k)). Qed.
Lemma lem4471169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471170 {A K : Type'} (k : K -> Prop) : (term258 A K k) = (term259 A K k).
Proof. exact (MK_COMB (@lem4471169) (@lem4471168 A K k)). Qed.
Lemma lem4471171 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term252 A K k s) = (term243 A K k s).
Proof. exact (eq_refl (term252 A K k s)). Qed.
Lemma lem4471172 {A K : Type'} (i : type732 A K) (s : type1470 A K) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4471173 {A K : Type'} (k : K -> Prop) (i : type732 A K) (s : type1470 A K) : (term260 A K k i s) = (term261 A K k i s).
Proof. exact (MK_COMB (@lem4471171 A K k s) (@lem4471172 A K i s)). Qed.
Lemma lem4471174 {A K : Type'} (k : K -> Prop) (i : type732 A K) (s : type1470 A K) : (term261 A K k i s) = (term262 A K k i s).
Proof. exact (eq_refl (term261 A K k i s)). Qed.
Lemma lem4471175 {A K : Type'} (k : K -> Prop) (i : type732 A K) (s : type1470 A K) : (term260 A K k i s) = (term262 A K k i s).
Proof. exact (TRANS (@lem4471173 A K k i s) (@lem4471174 A K k i s)). Qed.
Lemma lem4471176 {A K : Type'} (k : K -> Prop) (i : type732 A K) : (term263 A K k i) = (term264 A K k i).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4471175 A K k i s)). Qed.
Lemma lem4471177 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4471178 {A K : Type'} (k : K -> Prop) (i : type732 A K) : (term265 A K k i) = (term266 A K k i).
Proof. exact (MK_COMB (@lem4471177 A K) (@lem4471176 A K k i)). Qed.
Lemma lem4471179 {A K : Type'} (k : K -> Prop) : (term267 A K k) = (term268 A K k).
Proof. exact (fun_ext (fun i : type732 A K => @lem4471178 A K k i)). Qed.
Lemma lem4471180 {A K : Type'} : (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K)) = (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K))). Qed.
Lemma lem4471181 {A K : Type'} (k : K -> Prop) : (term250 A K k) = (term269 A K k).
Proof. exact (MK_COMB (@lem4471180 A K) (@lem4471179 A K k)). Qed.
Lemma lem4471182 {A K : Type'} (k : K -> Prop) : ((term249 A K k) = (term250 A K k)) = ((term246 A K k) = (term269 A K k)).
Proof. exact (MK_COMB (@lem4471170 A K k) (@lem4471181 A K k)). Qed.
Lemma lem4471183 {A K : Type'} (k : K -> Prop) : (term246 A K k) = (term269 A K k).
Proof. exact (EQ_MP (@lem4471182 A K k) (@lem4471157 A K k)). Qed.
Lemma lem4471184 {A K : Type'} (k : K -> Prop) : (term173 A K k) = (term269 A K k).
Proof. exact (TRANS (@lem4471153 A K k) (@lem4471183 A K k)). Qed.
Lemma lem4471185 {A K : Type'} : (term186 A K) = (term270 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471184 A K k)). Qed.
Lemma lem4471186 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471187 {A K : Type'} : (term197 A K) = (term271 A K).
Proof. exact (MK_COMB (@lem4471186 K) (@lem4471185 A K)). Qed.
Lemma lem4471189 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4471190 {A K : Type'} (P : type823 A K) : (term272 A K P) = (term273 A K P).
Proof. exact (@lem4471189 (K -> Prop) (type732 A K) P). Qed.
Lemma lem4471191 {A K : Type'} : (term274 A K) = (term275 A K).
Proof. exact (@lem4471190 A K (term276 A K)). Qed.
Lemma lem4471192 {A K : Type'} (k : K -> Prop) : (term277 A K k) = (term268 A K k).
Proof. exact (eq_refl (term277 A K k)). Qed.
Lemma lem4471193 {A K : Type'} (i : type732 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4471194 {A K : Type'} (k : K -> Prop) (i : type732 A K) : (term278 A K k i) = (term279 A K k i).
Proof. exact (MK_COMB (@lem4471192 A K k) (@lem4471193 A K i)). Qed.
Lemma lem4471195 {A K : Type'} (k : K -> Prop) (i : type732 A K) : (term279 A K k i) = (term266 A K k i).
Proof. exact (eq_refl (term279 A K k i)). Qed.
Lemma lem4471196 {A K : Type'} (k : K -> Prop) (i : type732 A K) : (term278 A K k i) = (term266 A K k i).
Proof. exact (TRANS (@lem4471194 A K k i) (@lem4471195 A K k i)). Qed.
Lemma lem4471197 {A K : Type'} (k : K -> Prop) : (term280 A K k) = (term268 A K k).
Proof. exact (fun_ext (fun i : type732 A K => @lem4471196 A K k i)). Qed.
Lemma lem4471198 {A K : Type'} : (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K)) = (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> A -> Prop) -> (K -> A -> Prop) -> K))). Qed.
Lemma lem4471199 {A K : Type'} (k : K -> Prop) : (term281 A K k) = (term269 A K k).
Proof. exact (MK_COMB (@lem4471198 A K) (@lem4471197 A K k)). Qed.
Lemma lem4471200 {A K : Type'} : (term282 A K) = (term270 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471199 A K k)). Qed.
Lemma lem4471201 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471202 {A K : Type'} : (term274 A K) = (term271 A K).
Proof. exact (MK_COMB (@lem4471201 K) (@lem4471200 A K)). Qed.
Lemma lem4471203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471204 {A K : Type'} : (term283 A K) = (term284 A K).
Proof. exact (MK_COMB (@lem4471203) (@lem4471202 A K)). Qed.
Lemma lem4471205 {A K : Type'} (k : K -> Prop) : (term277 A K k) = (term268 A K k).
Proof. exact (eq_refl (term277 A K k)). Qed.
Lemma lem4471206 {A K : Type'} (i : type843 A K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4471207 {A K : Type'} (i : type843 A K) (k : K -> Prop) : (term285 A K i k) = (term286 A K i k).
Proof. exact (MK_COMB (@lem4471205 A K k) (@lem4471206 A K i k)). Qed.
Lemma lem4471208 {A K : Type'} (i : type843 A K) (k : K -> Prop) : (term286 A K i k) = (term287 A K i k).
Proof. exact (eq_refl (term286 A K i k)). Qed.
Lemma lem4471209 {A K : Type'} (i : type843 A K) (k : K -> Prop) : (term285 A K i k) = (term287 A K i k).
Proof. exact (TRANS (@lem4471207 A K i k) (@lem4471208 A K i k)). Qed.
Lemma lem4471210 {A K : Type'} (i : type843 A K) : (term288 A K i) = (term289 A K i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471209 A K i k)). Qed.
Lemma lem4471211 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471212 {A K : Type'} (i : type843 A K) : (term290 A K i) = (term291 A K i).
Proof. exact (MK_COMB (@lem4471211 K) (@lem4471210 A K i)). Qed.
Lemma lem4471213 {A K : Type'} : (term292 A K) = (term293 A K).
Proof. exact (fun_ext (fun i : type843 A K => @lem4471212 A K i)). Qed.
Lemma lem4471214 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K))). Qed.
Lemma lem4471215 {A K : Type'} : (term275 A K) = (term294 A K).
Proof. exact (MK_COMB (@lem4471214 A K) (@lem4471213 A K)). Qed.
Lemma lem4471216 {A K : Type'} : ((term274 A K) = (term275 A K)) = ((term271 A K) = (term294 A K)).
Proof. exact (MK_COMB (@lem4471204 A K) (@lem4471215 A K)). Qed.
Lemma lem4471217 {A K : Type'} : (term271 A K) = (term294 A K).
Proof. exact (EQ_MP (@lem4471216 A K) (@lem4471191 A K)). Qed.
Lemma lem4471218 {A K : Type'} : (term197 A K) = (term294 A K).
Proof. exact (TRANS (@lem4471187 A K) (@lem4471217 A K)). Qed.
Lemma lem4471219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471220 {A K : Type'} : (term199 A K) = (term295 A K).
Proof. exact (MK_COMB (@lem4471219) (@lem4471218 A K)). Qed.
Lemma lem4471221 {A K : Type'} : (term202 A K) = (term202 A K).
Proof. exact (eq_refl (term202 A K)). Qed.
Lemma lem4471222 {A K : Type'} : (term203 A K) = (term296 A K).
Proof. exact (MK_COMB (@lem4471220 A K) (@lem4471221 A K)). Qed.
Lemma lem4471224 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4471225 {A K : Type'} (P : type217 A K) (Q : Prop) : (term297 A K P Q) = (term298 A K P Q).
Proof. exact (@lem4471224 (type843 A K) P Q). Qed.
Lemma lem4471226 {A K : Type'} : (term299 A K) = (term300 A K).
Proof. exact (@lem4471225 A K (term293 A K) (term202 A K)). Qed.
Lemma lem4471227 {A K : Type'} (i : type843 A K) : (term301 A K i) = (term291 A K i).
Proof. exact (eq_refl (term301 A K i)). Qed.
Lemma lem4471228 {A K : Type'} : (term302 A K) = (term293 A K).
Proof. exact (fun_ext (fun i : type843 A K => @lem4471227 A K i)). Qed.
Lemma lem4471229 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K))). Qed.
Lemma lem4471230 {A K : Type'} : (term303 A K) = (term294 A K).
Proof. exact (MK_COMB (@lem4471229 A K) (@lem4471228 A K)). Qed.
Lemma lem4471231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471232 {A K : Type'} : (term304 A K) = (term295 A K).
Proof. exact (MK_COMB (@lem4471231) (@lem4471230 A K)). Qed.
Lemma lem4471233 {A K : Type'} : (term202 A K) = (term202 A K).
Proof. exact (eq_refl (term202 A K)). Qed.
Lemma lem4471234 {A K : Type'} : (term299 A K) = (term296 A K).
Proof. exact (MK_COMB (@lem4471232 A K) (@lem4471233 A K)). Qed.
Lemma lem4471235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471236 {A K : Type'} : (term305 A K) = (term306 A K).
Proof. exact (MK_COMB (@lem4471235) (@lem4471234 A K)). Qed.
Lemma lem4471237 {A K : Type'} (i : type843 A K) : (term301 A K i) = (term291 A K i).
Proof. exact (eq_refl (term301 A K i)). Qed.
Lemma lem4471238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471239 {A K : Type'} (i : type843 A K) : (term307 A K i) = (term308 A K i).
Proof. exact (MK_COMB (@lem4471238) (@lem4471237 A K i)). Qed.
Lemma lem4471240 {A K : Type'} : (term202 A K) = (term202 A K).
Proof. exact (eq_refl (term202 A K)). Qed.
Lemma lem4471241 {A K : Type'} (i : type843 A K) : (term309 A K i) = (term310 A K i).
Proof. exact (MK_COMB (@lem4471239 A K i) (@lem4471240 A K)). Qed.
Lemma lem4471242 {A K : Type'} : (term311 A K) = (term312 A K).
Proof. exact (fun_ext (fun i : type843 A K => @lem4471241 A K i)). Qed.
Lemma lem4471243 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K))). Qed.
Lemma lem4471244 {A K : Type'} : (term300 A K) = (term313 A K).
Proof. exact (MK_COMB (@lem4471243 A K) (@lem4471242 A K)). Qed.
Lemma lem4471245 {A K : Type'} : ((term299 A K) = (term300 A K)) = ((term296 A K) = (term313 A K)).
Proof. exact (MK_COMB (@lem4471236 A K) (@lem4471244 A K)). Qed.
Lemma lem4471246 {A K : Type'} : (term296 A K) = (term313 A K).
Proof. exact (EQ_MP (@lem4471245 A K) (@lem4471226 A K)). Qed.
Lemma lem4471247 {A K : Type'} : (term203 A K) = (term313 A K).
Proof. exact (TRANS (@lem4471222 A K) (@lem4471246 A K)). Qed.
Lemma lem4471248 {A K : Type'} : (term133 A K) = (term313 A K).
Proof. exact (TRANS (@lem4471096 A K) (@lem4471247 A K)). Qed.
Lemma lem4471249 {A K : Type'} : (term26 A K) = (term313 A K).
Proof. exact (TRANS (@lem4470399 A K) (@lem4471248 A K)). Qed.
Lemma lem4471250 {A K : Type'} (h1 : term26 A K) : term313 A K.
Proof. exact (EQ_MP (@lem4471249 A K) (@lem4470202 A K h1)). Qed.
Lemma lem4471261 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term314 A K k s t i) = (term315 A K k s t i).
Proof. exact (@lem17362 (@IN K i k) (term316 A K s t i)). Qed.
Lemma lem4471266 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term51 A K k s t i) = (term317 A K k s t i).
Proof. exact (@lem17265 (@IN K i k) (term316 A K s t i)). Qed.
Lemma lem4471267 {K : Type'} (P : K -> Prop) : (term109 K P) = (term110 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4471268 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term318 A K k s t) = (term319 A K k s t).
Proof. exact (@lem4471267 K (term52 A K k s t)). Qed.
Lemma lem4471269 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term320 A K k s t i) = (term51 A K k s t i).
Proof. exact (eq_refl (term320 A K k s t i)). Qed.
Lemma lem4471270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4471271 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term321 A K k s t i) = (term314 A K k s t i).
Proof. exact (MK_COMB (@lem4471270) (@lem4471269 A K k s t i)). Qed.
Lemma lem4471272 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term321 A K k s t i) = (term315 A K k s t i).
Proof. exact (TRANS (@lem4471271 A K k s t i) (@lem4471261 A K k s t i)). Qed.
Lemma lem4471273 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term322 A K k s t) = (term323 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4471272 A K k s t i)). Qed.
Lemma lem4471274 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4471275 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term319 A K k s t) = (term324 A K k s t).
Proof. exact (MK_COMB (@lem4471274 K) (@lem4471273 A K k s t)). Qed.
Lemma lem4471276 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term318 A K k s t) = (term324 A K k s t).
Proof. exact (TRANS (@lem4471268 A K k s t) (@lem4471275 A K k s t)). Qed.
Lemma lem4471277 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term52 A K k s t) = (term325 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4471266 A K k s t i)). Qed.
Lemma lem4471278 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4471279 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term53 A K k s t) = (term326 A K k s t).
Proof. exact (MK_COMB (@lem4471278 K) (@lem4471277 A K k s t)). Qed.
Lemma lem4471281 {A K : Type'} (s : type1462 A K) (k : K -> Prop) (t : type1462 A K) : (term327 A K s k t) = (term327 A K s k t).
Proof. exact (eq_refl (term327 A K s k t)). Qed.
Lemma lem4471282 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term328 A K k s t) = (term329 A K k s t).
Proof. exact (MK_COMB (@lem4471281 A K s k t) (@lem4471279 A K k s t)). Qed.
Lemma lem4471284 {A K : Type'} (s : type1462 A K) (k : K -> Prop) (t : type1462 A K) : (term330 A K s k t) = (term330 A K s k t).
Proof. exact (eq_refl (term330 A K s k t)). Qed.
Lemma lem4471285 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term331 A K k s t) = (term332 A K k s t).
Proof. exact (MK_COMB (@lem4471284 A K s k t) (@lem4471276 A K k s t)). Qed.
Lemma lem4471286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471287 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term333 A K k s t) = (term334 A K k s t).
Proof. exact (MK_COMB (@lem4471286) (@lem4471285 A K k s t)). Qed.
Lemma lem4471288 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term335 A K k s t) = (term336 A K k s t).
Proof. exact (MK_COMB (@lem4471287 A K k s t) (@lem4471282 A K k s t)). Qed.
Lemma lem4471289 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : ((term55 A K s k t) = (term53 A K k s t)) = (term335 A K k s t).
Proof. exact (@lem17784 (term55 A K s k t) (term53 A K k s t)). Qed.
Lemma lem4471290 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : ((term55 A K s k t) = (term53 A K k s t)) = (term336 A K k s t).
Proof. exact (TRANS (@lem4471289 A K k s t) (@lem4471288 A K k s t)). Qed.
Lemma lem4471291 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term56 A K k s) = (term337 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4471290 A K k s t)). Qed.
Lemma lem4471292 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471293 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term57 A K k s) = (term338 A K k s).
Proof. exact (MK_COMB (@lem4471292 A K) (@lem4471291 A K k s)). Qed.
Lemma lem4471294 {A K : Type'} (k : K -> Prop) : (term58 A K k) = (term339 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4471293 A K k s)). Qed.
Lemma lem4471295 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471296 {A K : Type'} (k : K -> Prop) : (term59 A K k) = (term340 A K k).
Proof. exact (MK_COMB (@lem4471295 A K) (@lem4471294 A K k)). Qed.
Lemma lem4471297 {A K : Type'} : (term60 A K) = (term341 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471296 A K k)). Qed.
Lemma lem4471298 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471299 {A K : Type'} : (term27 A K) = (term342 A K).
Proof. exact (MK_COMB (@lem4471298 K) (@lem4471297 A K)). Qed.
Lemma lem4471309 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4471310 {A K : Type'} (P : type724 A K) (Q : type724 A K) : (term343 A K P Q) = (term344 A K P Q).
Proof. exact (@lem4471309 (type1462 A K) P Q). Qed.
Lemma lem4471311 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term345 A K k s) = (term346 A K k s).
Proof. exact (@lem4471310 A K (term347 A K k s) (term348 A K k s)). Qed.
Lemma lem4471312 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term349 A K k s t) = (term332 A K k s t).
Proof. exact (eq_refl (term349 A K k s t)). Qed.
Lemma lem4471313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471314 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term350 A K k s t) = (term334 A K k s t).
Proof. exact (MK_COMB (@lem4471313) (@lem4471312 A K k s t)). Qed.
Lemma lem4471315 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term351 A K k s t) = (term329 A K k s t).
Proof. exact (eq_refl (term351 A K k s t)). Qed.
Lemma lem4471316 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term352 A K k s t) = (term336 A K k s t).
Proof. exact (MK_COMB (@lem4471314 A K k s t) (@lem4471315 A K k s t)). Qed.
Lemma lem4471317 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term353 A K k s) = (term337 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4471316 A K k s t)). Qed.
Lemma lem4471318 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471319 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term345 A K k s) = (term338 A K k s).
Proof. exact (MK_COMB (@lem4471318 A K) (@lem4471317 A K k s)). Qed.
Lemma lem4471320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471321 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term354 A K k s) = (term355 A K k s).
Proof. exact (MK_COMB (@lem4471320) (@lem4471319 A K k s)). Qed.
Lemma lem4471322 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term349 A K k s t) = (term332 A K k s t).
Proof. exact (eq_refl (term349 A K k s t)). Qed.
Lemma lem4471323 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term356 A K k s) = (term347 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4471322 A K k s t)). Qed.
Lemma lem4471324 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471325 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term357 A K k s) = (term358 A K k s).
Proof. exact (MK_COMB (@lem4471324 A K) (@lem4471323 A K k s)). Qed.
Lemma lem4471326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471327 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term359 A K k s) = (term360 A K k s).
Proof. exact (MK_COMB (@lem4471326) (@lem4471325 A K k s)). Qed.
Lemma lem4471328 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term351 A K k s t) = (term329 A K k s t).
Proof. exact (eq_refl (term351 A K k s t)). Qed.
Lemma lem4471329 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term361 A K k s) = (term348 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4471328 A K k s t)). Qed.
Lemma lem4471330 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471331 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term362 A K k s) = (term363 A K k s).
Proof. exact (MK_COMB (@lem4471330 A K) (@lem4471329 A K k s)). Qed.
Lemma lem4471332 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term346 A K k s) = (term364 A K k s).
Proof. exact (MK_COMB (@lem4471327 A K k s) (@lem4471331 A K k s)). Qed.
Lemma lem4471333 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : ((term345 A K k s) = (term346 A K k s)) = ((term338 A K k s) = (term364 A K k s)).
Proof. exact (MK_COMB (@lem4471321 A K k s) (@lem4471332 A K k s)). Qed.
Lemma lem4471334 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term338 A K k s) = (term364 A K k s).
Proof. exact (EQ_MP (@lem4471333 A K k s) (@lem4471311 A K k s)). Qed.
Lemma lem4471527 {A K : Type'} (k : K -> Prop) : (term339 A K k) = (term365 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4471334 A K k s)). Qed.
Lemma lem4471528 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471529 {A K : Type'} (k : K -> Prop) : (term340 A K k) = (term366 A K k).
Proof. exact (MK_COMB (@lem4471528 A K) (@lem4471527 A K k)). Qed.
Lemma lem4471531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4471532 {A K : Type'} (P : type724 A K) (Q : type724 A K) : (term343 A K P Q) = (term344 A K P Q).
Proof. exact (@lem4471531 (type1462 A K) P Q). Qed.
Lemma lem4471533 {A K : Type'} (k : K -> Prop) : (term367 A K k) = (term368 A K k).
Proof. exact (@lem4471532 A K (term369 A K k) (term370 A K k)). Qed.
Lemma lem4471534 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term371 A K k s) = (term358 A K k s).
Proof. exact (eq_refl (term371 A K k s)). Qed.
Lemma lem4471535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471536 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term372 A K k s) = (term360 A K k s).
Proof. exact (MK_COMB (@lem4471535) (@lem4471534 A K k s)). Qed.
Lemma lem4471537 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term373 A K k s) = (term363 A K k s).
Proof. exact (eq_refl (term373 A K k s)). Qed.
Lemma lem4471538 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term374 A K k s) = (term364 A K k s).
Proof. exact (MK_COMB (@lem4471536 A K k s) (@lem4471537 A K k s)). Qed.
Lemma lem4471539 {A K : Type'} (k : K -> Prop) : (term375 A K k) = (term365 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4471538 A K k s)). Qed.
Lemma lem4471540 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471541 {A K : Type'} (k : K -> Prop) : (term367 A K k) = (term366 A K k).
Proof. exact (MK_COMB (@lem4471540 A K) (@lem4471539 A K k)). Qed.
Lemma lem4471542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471543 {A K : Type'} (k : K -> Prop) : (term376 A K k) = (term377 A K k).
Proof. exact (MK_COMB (@lem4471542) (@lem4471541 A K k)). Qed.
Lemma lem4471544 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term371 A K k s) = (term358 A K k s).
Proof. exact (eq_refl (term371 A K k s)). Qed.
Lemma lem4471545 {A K : Type'} (k : K -> Prop) : (term378 A K k) = (term369 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4471544 A K k s)). Qed.
Lemma lem4471546 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471547 {A K : Type'} (k : K -> Prop) : (term379 A K k) = (term380 A K k).
Proof. exact (MK_COMB (@lem4471546 A K) (@lem4471545 A K k)). Qed.
Lemma lem4471548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471549 {A K : Type'} (k : K -> Prop) : (term381 A K k) = (term382 A K k).
Proof. exact (MK_COMB (@lem4471548) (@lem4471547 A K k)). Qed.
Lemma lem4471550 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term373 A K k s) = (term363 A K k s).
Proof. exact (eq_refl (term373 A K k s)). Qed.
Lemma lem4471551 {A K : Type'} (k : K -> Prop) : (term383 A K k) = (term370 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4471550 A K k s)). Qed.
Lemma lem4471552 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4471553 {A K : Type'} (k : K -> Prop) : (term384 A K k) = (term385 A K k).
Proof. exact (MK_COMB (@lem4471552 A K) (@lem4471551 A K k)). Qed.
Lemma lem4471554 {A K : Type'} (k : K -> Prop) : (term368 A K k) = (term386 A K k).
Proof. exact (MK_COMB (@lem4471549 A K k) (@lem4471553 A K k)). Qed.
Lemma lem4471555 {A K : Type'} (k : K -> Prop) : ((term367 A K k) = (term368 A K k)) = ((term366 A K k) = (term386 A K k)).
Proof. exact (MK_COMB (@lem4471543 A K k) (@lem4471554 A K k)). Qed.
Lemma lem4471556 {A K : Type'} (k : K -> Prop) : (term366 A K k) = (term386 A K k).
Proof. exact (EQ_MP (@lem4471555 A K k) (@lem4471533 A K k)). Qed.
Lemma lem4471757 {A K : Type'} (k : K -> Prop) : (term340 A K k) = (term386 A K k).
Proof. exact (TRANS (@lem4471529 A K k) (@lem4471556 A K k)). Qed.
Lemma lem4471758 {A K : Type'} : (term341 A K) = (term387 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471757 A K k)). Qed.
Lemma lem4471759 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471760 {A K : Type'} : (term342 A K) = (term388 A K).
Proof. exact (MK_COMB (@lem4471759 K) (@lem4471758 A K)). Qed.
Lemma lem4471762 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4471763 {K : Type'} (P : type686 K) (Q : type686 K) : (term182 K P Q) = (term183 K P Q).
Proof. exact (@lem4471762 (K -> Prop) P Q). Qed.
Lemma lem4471764 {A K : Type'} : (term389 A K) = (term390 A K).
Proof. exact (@lem4471763 K (term391 A K) (term392 A K)). Qed.
Lemma lem4471765 {A K : Type'} (k : K -> Prop) : (term393 A K k) = (term380 A K k).
Proof. exact (eq_refl (term393 A K k)). Qed.
Lemma lem4471766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471767 {A K : Type'} (k : K -> Prop) : (term394 A K k) = (term382 A K k).
Proof. exact (MK_COMB (@lem4471766) (@lem4471765 A K k)). Qed.
Lemma lem4471768 {A K : Type'} (k : K -> Prop) : (term395 A K k) = (term385 A K k).
Proof. exact (eq_refl (term395 A K k)). Qed.
Lemma lem4471769 {A K : Type'} (k : K -> Prop) : (term396 A K k) = (term386 A K k).
Proof. exact (MK_COMB (@lem4471767 A K k) (@lem4471768 A K k)). Qed.
Lemma lem4471770 {A K : Type'} : (term397 A K) = (term387 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471769 A K k)). Qed.
Lemma lem4471771 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471772 {A K : Type'} : (term389 A K) = (term388 A K).
Proof. exact (MK_COMB (@lem4471771 K) (@lem4471770 A K)). Qed.
Lemma lem4471773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4471774 {A K : Type'} : (term398 A K) = (term399 A K).
Proof. exact (MK_COMB (@lem4471773) (@lem4471772 A K)). Qed.
Lemma lem4471775 {A K : Type'} (k : K -> Prop) : (term393 A K k) = (term380 A K k).
Proof. exact (eq_refl (term393 A K k)). Qed.
Lemma lem4471776 {A K : Type'} : (term400 A K) = (term391 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471775 A K k)). Qed.
Lemma lem4471777 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471778 {A K : Type'} : (term401 A K) = (term402 A K).
Proof. exact (MK_COMB (@lem4471777 K) (@lem4471776 A K)). Qed.
Lemma lem4471779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4471780 {A K : Type'} : (term403 A K) = (term404 A K).
Proof. exact (MK_COMB (@lem4471779) (@lem4471778 A K)). Qed.
Lemma lem4471781 {A K : Type'} (k : K -> Prop) : (term395 A K k) = (term385 A K k).
Proof. exact (eq_refl (term395 A K k)). Qed.
Lemma lem4471782 {A K : Type'} : (term405 A K) = (term392 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4471781 A K k)). Qed.
Lemma lem4471783 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4471784 {A K : Type'} : (term406 A K) = (term407 A K).
Proof. exact (MK_COMB (@lem4471783 K) (@lem4471782 A K)). Qed.
Lemma lem4471785 {A K : Type'} : (term390 A K) = (term408 A K).
Proof. exact (MK_COMB (@lem4471780 A K) (@lem4471784 A K)). Qed.
Lemma lem4471786 {A K : Type'} : ((term389 A K) = (term390 A K)) = ((term388 A K) = (term408 A K)).
Proof. exact (MK_COMB (@lem4471774 A K) (@lem4471785 A K)). Qed.
Lemma lem4471787 {A K : Type'} : (term388 A K) = (term408 A K).
Proof. exact (EQ_MP (@lem4471786 A K) (@lem4471764 A K)). Qed.
Lemma lem4471996 {A K : Type'} : (term342 A K) = (term408 A K).
Proof. exact (TRANS (@lem4471760 A K) (@lem4471787 A K)). Qed.
Lemma lem4471998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4471999 {K : Type'} (P : Prop) (Q : K -> Prop) : (term204 K P Q) = (term205 K P Q).
Proof. exact (@lem4471998 K P Q). Qed.
Lemma lem4472000 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term409 A K k s t) = (term410 A K k s t).
Proof. exact (@lem4471999 K (term55 A K s k t) (term323 A K k s t)). Qed.
Lemma lem4472001 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term411 A K k s t i) = (term315 A K k s t i).
Proof. exact (eq_refl (term411 A K k s t i)). Qed.
Lemma lem4472002 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term412 A K k s t) = (term323 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4472001 A K k s t i)). Qed.
Lemma lem4472003 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4472004 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term413 A K k s t) = (term324 A K k s t).
Proof. exact (MK_COMB (@lem4472003 K) (@lem4472002 A K k s t)). Qed.
Lemma lem4472005 {A K : Type'} (s : type1462 A K) (k : K -> Prop) (t : type1462 A K) : (term330 A K s k t) = (term330 A K s k t).
Proof. exact (eq_refl (term330 A K s k t)). Qed.
Lemma lem4472006 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term409 A K k s t) = (term332 A K k s t).
Proof. exact (MK_COMB (@lem4472005 A K s k t) (@lem4472004 A K k s t)). Qed.
Lemma lem4472007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4472008 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term414 A K k s t) = (term415 A K k s t).
Proof. exact (MK_COMB (@lem4472007) (@lem4472006 A K k s t)). Qed.
Lemma lem4472009 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term411 A K k s t i) = (term315 A K k s t i).
Proof. exact (eq_refl (term411 A K k s t i)). Qed.
Lemma lem4472010 {A K : Type'} (s : type1462 A K) (k : K -> Prop) (t : type1462 A K) : (term330 A K s k t) = (term330 A K s k t).
Proof. exact (eq_refl (term330 A K s k t)). Qed.
Lemma lem4472011 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term416 A K k s t i) = (term417 A K k s t i).
Proof. exact (MK_COMB (@lem4472010 A K s k t) (@lem4472009 A K k s t i)). Qed.
Lemma lem4472012 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term418 A K k s t) = (term419 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4472011 A K k s t i)). Qed.
Lemma lem4472013 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4472014 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term410 A K k s t) = (term420 A K k s t).
Proof. exact (MK_COMB (@lem4472013 K) (@lem4472012 A K k s t)). Qed.
Lemma lem4472015 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : ((term409 A K k s t) = (term410 A K k s t)) = ((term332 A K k s t) = (term420 A K k s t)).
Proof. exact (MK_COMB (@lem4472008 A K k s t) (@lem4472014 A K k s t)). Qed.
Lemma lem4472016 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term332 A K k s t) = (term420 A K k s t).
Proof. exact (EQ_MP (@lem4472015 A K k s t) (@lem4472000 A K k s t)). Qed.
Lemma lem4472017 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term347 A K k s) = (term421 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4472016 A K k s t)). Qed.
Lemma lem4472018 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472019 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term358 A K k s) = (term422 A K k s).
Proof. exact (MK_COMB (@lem4472018 A K) (@lem4472017 A K k s)). Qed.
Lemma lem4472021 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4472022 {A K : Type'} (P : type722 A K) : (term423 A K P) = (term424 A K P).
Proof. exact (@lem4472021 (type1462 A K) K P). Qed.
Lemma lem4472023 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term425 A K k s) = (term426 A K k s).
Proof. exact (@lem4472022 A K (term427 A K k s)). Qed.
Lemma lem4472024 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term428 A K k s t) = (term419 A K k s t).
Proof. exact (eq_refl (term428 A K k s t)). Qed.
Lemma lem4472025 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4472026 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term429 A K k s t i) = (term430 A K k s t i).
Proof. exact (MK_COMB (@lem4472024 A K k s t) (@lem4472025 K i)). Qed.
Lemma lem4472027 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term430 A K k s t i) = (term417 A K k s t i).
Proof. exact (eq_refl (term430 A K k s t i)). Qed.
Lemma lem4472028 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) (i : K) : (term429 A K k s t i) = (term417 A K k s t i).
Proof. exact (TRANS (@lem4472026 A K k s t i) (@lem4472027 A K k s t i)). Qed.
Lemma lem4472029 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term431 A K k s t) = (term419 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4472028 A K k s t i)). Qed.
Lemma lem4472030 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4472031 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term432 A K k s t) = (term420 A K k s t).
Proof. exact (MK_COMB (@lem4472030 K) (@lem4472029 A K k s t)). Qed.
Lemma lem4472032 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term433 A K k s) = (term421 A K k s).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4472031 A K k s t)). Qed.
Lemma lem4472033 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472034 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term425 A K k s) = (term422 A K k s).
Proof. exact (MK_COMB (@lem4472033 A K) (@lem4472032 A K k s)). Qed.
Lemma lem4472035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4472036 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term434 A K k s) = (term435 A K k s).
Proof. exact (MK_COMB (@lem4472035) (@lem4472034 A K k s)). Qed.
Lemma lem4472037 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (t : type1462 A K) : (term428 A K k s t) = (term419 A K k s t).
Proof. exact (eq_refl (term428 A K k s t)). Qed.
Lemma lem4472038 {A K : Type'} (i : type723 A K) (t : type1462 A K) : (i t) = (i t).
Proof. exact (eq_refl (i t)). Qed.
Lemma lem4472039 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) (t : type1462 A K) : (term436 A K k s i t) = (term437 A K k s i t).
Proof. exact (MK_COMB (@lem4472037 A K k s t) (@lem4472038 A K i t)). Qed.
Lemma lem4472040 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) (t : type1462 A K) : (term437 A K k s i t) = (term438 A K k s i t).
Proof. exact (eq_refl (term437 A K k s i t)). Qed.
Lemma lem4472041 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) (t : type1462 A K) : (term436 A K k s i t) = (term438 A K k s i t).
Proof. exact (TRANS (@lem4472039 A K k s i t) (@lem4472040 A K k s i t)). Qed.
Lemma lem4472042 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) : (term439 A K k s i) = (term440 A K k s i).
Proof. exact (fun_ext (fun t : type1462 A K => @lem4472041 A K k s i t)). Qed.
Lemma lem4472043 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472044 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) : (term441 A K k s i) = (term442 A K k s i).
Proof. exact (MK_COMB (@lem4472043 A K) (@lem4472042 A K k s i)). Qed.
Lemma lem4472045 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term443 A K k s) = (term444 A K k s).
Proof. exact (fun_ext (fun i : type723 A K => @lem4472044 A K k s i)). Qed.
Lemma lem4472046 {A K : Type'} : (@ex ((K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472047 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term426 A K k s) = (term445 A K k s).
Proof. exact (MK_COMB (@lem4472046 A K) (@lem4472045 A K k s)). Qed.
Lemma lem4472048 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : ((term425 A K k s) = (term426 A K k s)) = ((term422 A K k s) = (term445 A K k s)).
Proof. exact (MK_COMB (@lem4472036 A K k s) (@lem4472047 A K k s)). Qed.
Lemma lem4472049 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term422 A K k s) = (term445 A K k s).
Proof. exact (EQ_MP (@lem4472048 A K k s) (@lem4472023 A K k s)). Qed.
Lemma lem4472050 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term358 A K k s) = (term445 A K k s).
Proof. exact (TRANS (@lem4472019 A K k s) (@lem4472049 A K k s)). Qed.
Lemma lem4472051 {A K : Type'} (k : K -> Prop) : (term369 A K k) = (term446 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4472050 A K k s)). Qed.
Lemma lem4472052 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472053 {A K : Type'} (k : K -> Prop) : (term380 A K k) = (term447 A K k).
Proof. exact (MK_COMB (@lem4472052 A K) (@lem4472051 A K k)). Qed.
Lemma lem4472055 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4472056 {A K : Type'} (P : type720 A K) : (term448 A K P) = (term449 A K P).
Proof. exact (@lem4472055 (type1462 A K) (type723 A K) P). Qed.
Lemma lem4472057 {A K : Type'} (k : K -> Prop) : (term450 A K k) = (term451 A K k).
Proof. exact (@lem4472056 A K (term452 A K k)). Qed.
Lemma lem4472058 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term453 A K k s) = (term444 A K k s).
Proof. exact (eq_refl (term453 A K k s)). Qed.
Lemma lem4472059 {A K : Type'} (i : type723 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4472060 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) : (term454 A K k s i) = (term455 A K k s i).
Proof. exact (MK_COMB (@lem4472058 A K k s) (@lem4472059 A K i)). Qed.
Lemma lem4472061 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) : (term455 A K k s i) = (term442 A K k s i).
Proof. exact (eq_refl (term455 A K k s i)). Qed.
Lemma lem4472062 {A K : Type'} (k : K -> Prop) (s : type1462 A K) (i : type723 A K) : (term454 A K k s i) = (term442 A K k s i).
Proof. exact (TRANS (@lem4472060 A K k s i) (@lem4472061 A K k s i)). Qed.
Lemma lem4472063 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term456 A K k s) = (term444 A K k s).
Proof. exact (fun_ext (fun i : type723 A K => @lem4472062 A K k s i)). Qed.
Lemma lem4472064 {A K : Type'} : (@ex ((K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472065 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term457 A K k s) = (term445 A K k s).
Proof. exact (MK_COMB (@lem4472064 A K) (@lem4472063 A K k s)). Qed.
Lemma lem4472066 {A K : Type'} (k : K -> Prop) : (term458 A K k) = (term446 A K k).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4472065 A K k s)). Qed.
Lemma lem4472067 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472068 {A K : Type'} (k : K -> Prop) : (term450 A K k) = (term447 A K k).
Proof. exact (MK_COMB (@lem4472067 A K) (@lem4472066 A K k)). Qed.
Lemma lem4472069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4472070 {A K : Type'} (k : K -> Prop) : (term459 A K k) = (term460 A K k).
Proof. exact (MK_COMB (@lem4472069) (@lem4472068 A K k)). Qed.
Lemma lem4472071 {A K : Type'} (k : K -> Prop) (s : type1462 A K) : (term453 A K k s) = (term444 A K k s).
Proof. exact (eq_refl (term453 A K k s)). Qed.
Lemma lem4472072 {A K : Type'} (i : type721 A K) (s : type1462 A K) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4472073 {A K : Type'} (k : K -> Prop) (i : type721 A K) (s : type1462 A K) : (term461 A K k i s) = (term462 A K k i s).
Proof. exact (MK_COMB (@lem4472071 A K k s) (@lem4472072 A K i s)). Qed.
Lemma lem4472074 {A K : Type'} (k : K -> Prop) (i : type721 A K) (s : type1462 A K) : (term462 A K k i s) = (term463 A K k i s).
Proof. exact (eq_refl (term462 A K k i s)). Qed.
Lemma lem4472075 {A K : Type'} (k : K -> Prop) (i : type721 A K) (s : type1462 A K) : (term461 A K k i s) = (term463 A K k i s).
Proof. exact (TRANS (@lem4472073 A K k i s) (@lem4472074 A K k i s)). Qed.
Lemma lem4472076 {A K : Type'} (k : K -> Prop) (i : type721 A K) : (term464 A K k i) = (term465 A K k i).
Proof. exact (fun_ext (fun s : type1462 A K => @lem4472075 A K k i s)). Qed.
Lemma lem4472077 {A K : Type'} : (@all (K -> (prod K A) -> Prop)) = (@all (K -> (prod K A) -> Prop)).
Proof. exact (eq_refl (@all (K -> (prod K A) -> Prop))). Qed.
Lemma lem4472078 {A K : Type'} (k : K -> Prop) (i : type721 A K) : (term466 A K k i) = (term467 A K k i).
Proof. exact (MK_COMB (@lem4472077 A K) (@lem4472076 A K k i)). Qed.
Lemma lem4472079 {A K : Type'} (k : K -> Prop) : (term468 A K k) = (term469 A K k).
Proof. exact (fun_ext (fun i : type721 A K => @lem4472078 A K k i)). Qed.
Lemma lem4472080 {A K : Type'} : (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472081 {A K : Type'} (k : K -> Prop) : (term451 A K k) = (term470 A K k).
Proof. exact (MK_COMB (@lem4472080 A K) (@lem4472079 A K k)). Qed.
Lemma lem4472082 {A K : Type'} (k : K -> Prop) : ((term450 A K k) = (term451 A K k)) = ((term447 A K k) = (term470 A K k)).
Proof. exact (MK_COMB (@lem4472070 A K k) (@lem4472081 A K k)). Qed.
Lemma lem4472083 {A K : Type'} (k : K -> Prop) : (term447 A K k) = (term470 A K k).
Proof. exact (EQ_MP (@lem4472082 A K k) (@lem4472057 A K k)). Qed.
Lemma lem4472084 {A K : Type'} (k : K -> Prop) : (term380 A K k) = (term470 A K k).
Proof. exact (TRANS (@lem4472053 A K k) (@lem4472083 A K k)). Qed.
Lemma lem4472085 {A K : Type'} : (term391 A K) = (term471 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472084 A K k)). Qed.
Lemma lem4472086 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472087 {A K : Type'} : (term402 A K) = (term472 A K).
Proof. exact (MK_COMB (@lem4472086 K) (@lem4472085 A K)). Qed.
Lemma lem4472089 {A B : Type'} (P : type1413 A B) : (term220 A B P) = (term221 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4472090 {A K : Type'} (P : type822 A K) : (term473 A K P) = (term474 A K P).
Proof. exact (@lem4472089 (K -> Prop) (type721 A K) P). Qed.
Lemma lem4472091 {A K : Type'} : (term475 A K) = (term476 A K).
Proof. exact (@lem4472090 A K (term477 A K)). Qed.
Lemma lem4472092 {A K : Type'} (k : K -> Prop) : (term478 A K k) = (term469 A K k).
Proof. exact (eq_refl (term478 A K k)). Qed.
Lemma lem4472093 {A K : Type'} (i : type721 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4472094 {A K : Type'} (k : K -> Prop) (i : type721 A K) : (term479 A K k i) = (term480 A K k i).
Proof. exact (MK_COMB (@lem4472092 A K k) (@lem4472093 A K i)). Qed.
Lemma lem4472095 {A K : Type'} (k : K -> Prop) (i : type721 A K) : (term480 A K k i) = (term467 A K k i).
Proof. exact (eq_refl (term480 A K k i)). Qed.
Lemma lem4472096 {A K : Type'} (k : K -> Prop) (i : type721 A K) : (term479 A K k i) = (term467 A K k i).
Proof. exact (TRANS (@lem4472094 A K k i) (@lem4472095 A K k i)). Qed.
Lemma lem4472097 {A K : Type'} (k : K -> Prop) : (term481 A K k) = (term469 A K k).
Proof. exact (fun_ext (fun i : type721 A K => @lem4472096 A K k i)). Qed.
Lemma lem4472098 {A K : Type'} : (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472099 {A K : Type'} (k : K -> Prop) : (term482 A K k) = (term470 A K k).
Proof. exact (MK_COMB (@lem4472098 A K) (@lem4472097 A K k)). Qed.
Lemma lem4472100 {A K : Type'} : (term483 A K) = (term471 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472099 A K k)). Qed.
Lemma lem4472101 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472102 {A K : Type'} : (term475 A K) = (term472 A K).
Proof. exact (MK_COMB (@lem4472101 K) (@lem4472100 A K)). Qed.
Lemma lem4472103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4472104 {A K : Type'} : (term484 A K) = (term485 A K).
Proof. exact (MK_COMB (@lem4472103) (@lem4472102 A K)). Qed.
Lemma lem4472105 {A K : Type'} (k : K -> Prop) : (term478 A K k) = (term469 A K k).
Proof. exact (eq_refl (term478 A K k)). Qed.
Lemma lem4472106 {A K : Type'} (i : type842 A K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4472107 {A K : Type'} (i : type842 A K) (k : K -> Prop) : (term486 A K i k) = (term487 A K i k).
Proof. exact (MK_COMB (@lem4472105 A K k) (@lem4472106 A K i k)). Qed.
Lemma lem4472108 {A K : Type'} (i : type842 A K) (k : K -> Prop) : (term487 A K i k) = (term488 A K i k).
Proof. exact (eq_refl (term487 A K i k)). Qed.
Lemma lem4472109 {A K : Type'} (i : type842 A K) (k : K -> Prop) : (term486 A K i k) = (term488 A K i k).
Proof. exact (TRANS (@lem4472107 A K i k) (@lem4472108 A K i k)). Qed.
Lemma lem4472110 {A K : Type'} (i : type842 A K) : (term489 A K i) = (term490 A K i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472109 A K i k)). Qed.
Lemma lem4472111 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472112 {A K : Type'} (i : type842 A K) : (term491 A K i) = (term492 A K i).
Proof. exact (MK_COMB (@lem4472111 K) (@lem4472110 A K i)). Qed.
Lemma lem4472113 {A K : Type'} : (term493 A K) = (term494 A K).
Proof. exact (fun_ext (fun i : type842 A K => @lem4472112 A K i)). Qed.
Lemma lem4472114 {A K : Type'} : (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472115 {A K : Type'} : (term476 A K) = (term495 A K).
Proof. exact (MK_COMB (@lem4472114 A K) (@lem4472113 A K)). Qed.
Lemma lem4472116 {A K : Type'} : ((term475 A K) = (term476 A K)) = ((term472 A K) = (term495 A K)).
Proof. exact (MK_COMB (@lem4472104 A K) (@lem4472115 A K)). Qed.
Lemma lem4472117 {A K : Type'} : (term472 A K) = (term495 A K).
Proof. exact (EQ_MP (@lem4472116 A K) (@lem4472091 A K)). Qed.
Lemma lem4472118 {A K : Type'} : (term402 A K) = (term495 A K).
Proof. exact (TRANS (@lem4472087 A K) (@lem4472117 A K)). Qed.
Lemma lem4472119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472120 {A K : Type'} : (term404 A K) = (term496 A K).
Proof. exact (MK_COMB (@lem4472119) (@lem4472118 A K)). Qed.
Lemma lem4472121 {A K : Type'} : (term407 A K) = (term407 A K).
Proof. exact (eq_refl (term407 A K)). Qed.
Lemma lem4472122 {A K : Type'} : (term408 A K) = (term497 A K).
Proof. exact (MK_COMB (@lem4472120 A K) (@lem4472121 A K)). Qed.
Lemma lem4472124 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4472125 {A K : Type'} (P : type216 A K) (Q : Prop) : (term498 A K P Q) = (term499 A K P Q).
Proof. exact (@lem4472124 (type842 A K) P Q). Qed.
Lemma lem4472126 {A K : Type'} : (term500 A K) = (term501 A K).
Proof. exact (@lem4472125 A K (term494 A K) (term407 A K)). Qed.
Lemma lem4472127 {A K : Type'} (i : type842 A K) : (term502 A K i) = (term492 A K i).
Proof. exact (eq_refl (term502 A K i)). Qed.
Lemma lem4472128 {A K : Type'} : (term503 A K) = (term494 A K).
Proof. exact (fun_ext (fun i : type842 A K => @lem4472127 A K i)). Qed.
Lemma lem4472129 {A K : Type'} : (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472130 {A K : Type'} : (term504 A K) = (term495 A K).
Proof. exact (MK_COMB (@lem4472129 A K) (@lem4472128 A K)). Qed.
Lemma lem4472131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472132 {A K : Type'} : (term505 A K) = (term496 A K).
Proof. exact (MK_COMB (@lem4472131) (@lem4472130 A K)). Qed.
Lemma lem4472133 {A K : Type'} : (term407 A K) = (term407 A K).
Proof. exact (eq_refl (term407 A K)). Qed.
Lemma lem4472134 {A K : Type'} : (term500 A K) = (term497 A K).
Proof. exact (MK_COMB (@lem4472132 A K) (@lem4472133 A K)). Qed.
Lemma lem4472135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4472136 {A K : Type'} : (term506 A K) = (term507 A K).
Proof. exact (MK_COMB (@lem4472135) (@lem4472134 A K)). Qed.
Lemma lem4472137 {A K : Type'} (i : type842 A K) : (term502 A K i) = (term492 A K i).
Proof. exact (eq_refl (term502 A K i)). Qed.
Lemma lem4472138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472139 {A K : Type'} (i : type842 A K) : (term508 A K i) = (term509 A K i).
Proof. exact (MK_COMB (@lem4472138) (@lem4472137 A K i)). Qed.
Lemma lem4472140 {A K : Type'} : (term407 A K) = (term407 A K).
Proof. exact (eq_refl (term407 A K)). Qed.
Lemma lem4472141 {A K : Type'} (i : type842 A K) : (term510 A K i) = (term511 A K i).
Proof. exact (MK_COMB (@lem4472139 A K i) (@lem4472140 A K)). Qed.
Lemma lem4472142 {A K : Type'} : (term512 A K) = (term513 A K).
Proof. exact (fun_ext (fun i : type842 A K => @lem4472141 A K i)). Qed.
Lemma lem4472143 {A K : Type'} : (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)) = (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> (prod K A) -> Prop) -> (K -> (prod K A) -> Prop) -> K))). Qed.
Lemma lem4472144 {A K : Type'} : (term501 A K) = (term514 A K).
Proof. exact (MK_COMB (@lem4472143 A K) (@lem4472142 A K)). Qed.
Lemma lem4472145 {A K : Type'} : ((term500 A K) = (term501 A K)) = ((term497 A K) = (term514 A K)).
Proof. exact (MK_COMB (@lem4472136 A K) (@lem4472144 A K)). Qed.
Lemma lem4472146 {A K : Type'} : (term497 A K) = (term514 A K).
Proof. exact (EQ_MP (@lem4472145 A K) (@lem4472126 A K)). Qed.
Lemma lem4472147 {A K : Type'} : (term408 A K) = (term514 A K).
Proof. exact (TRANS (@lem4472122 A K) (@lem4472146 A K)). Qed.
Lemma lem4472148 {A K : Type'} : (term342 A K) = (term514 A K).
Proof. exact (TRANS (@lem4471996 A K) (@lem4472147 A K)). Qed.
Lemma lem4472149 {A K : Type'} : (term27 A K) = (term514 A K).
Proof. exact (TRANS (@lem4471299 A K) (@lem4472148 A K)). Qed.
Lemma lem4472150 {A K : Type'} (h1 : term27 A K) : term514 A K.
Proof. exact (EQ_MP (@lem4472149 A K) (@lem4470203 A K h1)). Qed.
Lemma lem4472152 {A K : Type'} (i' : type843 A K) (h1 : term310 A K i') : term310 A K i'.
Proof. exact (h1). Qed.
Lemma lem4472153 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term103 A K t u k s.
Proof. exact (h1). Qed.
Lemma lem4472466 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem4472471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472472 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472471 K (A -> Prop) f x). Qed.
Lemma lem4472474 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4472472 A K s i). Qed.
Lemma lem4472479 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472480 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472479 K (A -> Prop) f x). Qed.
Lemma lem4472482 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4472480 A K t i). Qed.
Lemma lem4472483 {A K : Type'} (s : type1470 A K) (i : K) : (term515 A K s i) = (term516 A K s i).
Proof. exact (MK_COMB (@lem4472466 A) (@lem4472474 A K s i)). Qed.
Lemma lem4472484 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term77 A K s t i) = (term517 A K s t i).
Proof. exact (MK_COMB (@lem4472483 A K s i) (@lem4472482 A K t i)). Qed.
Lemma lem4472486 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472487 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4472486 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4472488 {A K : Type'} (s : type1470 A K) (i : K) : (term516 A K s i) = (term518 A K s i).
Proof. exact (@lem4472487 A (@SUBSET A) (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4472489 {A K : Type'} (t : type1470 A K) (i : K) : (@I (K -> A -> Prop) t i) = (@I (K -> A -> Prop) t i).
Proof. exact (eq_refl (@I (K -> A -> Prop) t i)). Qed.
Lemma lem4472490 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term517 A K s t i) = (term519 A K s t i).
Proof. exact (MK_COMB (@lem4472488 A K s i) (@lem4472489 A K t i)). Qed.
Lemma lem4472492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472493 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4472492 (A -> Prop) Prop f x). Qed.
Lemma lem4472494 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term519 A K s t i) = (term520 A K s t i).
Proof. exact (@lem4472493 A (term518 A K s i) (@I (K -> A -> Prop) t i)). Qed.
Lemma lem4472495 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term517 A K s t i) = (term520 A K s t i).
Proof. exact (TRANS (@lem4472490 A K s t i) (@lem4472494 A K s t i)). Qed.
Lemma lem4472496 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term77 A K s t i) = (term520 A K s t i).
Proof. exact (TRANS (@lem4472484 A K s t i) (@lem4472495 A K s t i)). Qed.
Lemma lem4472497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4472504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472505 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4472504 K (type686 K) f x). Qed.
Lemma lem4472506 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4472505 K (@IN K) i). Qed.
Lemma lem4472507 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4472508 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4472506 K i) (@lem4472507 K k)). Qed.
Lemma lem4472510 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472511 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4472510 (K -> Prop) Prop f x). Qed.
Lemma lem4472512 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term521 K i k).
Proof. exact (@lem4472511 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4472514 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term521 K i k).
Proof. exact (TRANS (@lem4472508 K i k) (@lem4472512 K i k)). Qed.
Lemma lem4472515 {K : Type'} (i : K) (k : K -> Prop) : (term522 K i k) = (term523 K i k).
Proof. exact (MK_COMB (@lem4472497) (@lem4472514 K i k)). Qed.
Lemma lem4472516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4472517 {K : Type'} (i : K) (k : K -> Prop) : (term524 K i k) = (term525 K i k).
Proof. exact (MK_COMB (@lem4472516) (@lem4472515 K i k)). Qed.
Lemma lem4472518 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term76 A K k s t i) = (term526 A K k s t i).
Proof. exact (MK_COMB (@lem4472517 K i k) (@lem4472496 A K s t i)). Qed.
Lemma lem4472519 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term78 A K k s t) = (term527 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4472518 A K k s t i)). Qed.
Lemma lem4472520 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4472521 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term79 A K k s t) = (term528 A K k s t).
Proof. exact (MK_COMB (@lem4472520 K) (@lem4472519 A K k s t)). Qed.
Lemma lem4472522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4472523 {A K : Type'} : (@SUBSET (prod K A)) = (@SUBSET (prod K A)).
Proof. exact (eq_refl (@SUBSET (prod K A))). Qed.
Lemma lem4472530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472531 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472530 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472532 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472531 A K (@disjoint_union A K) k). Qed.
Lemma lem4472533 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472534 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s).
Proof. exact (MK_COMB (@lem4472532 A K k) (@lem4472533 A K s)). Qed.
Lemma lem4472536 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472537 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472536 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472538 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s) = (term529 A K k s).
Proof. exact (@lem4472537 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) s). Qed.
Lemma lem4472540 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term529 A K k s).
Proof. exact (TRANS (@lem4472534 A K k s) (@lem4472538 A K k s)). Qed.
Lemma lem4472547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472548 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472547 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472549 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472548 A K (@disjoint_union A K) k). Qed.
Lemma lem4472550 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472551 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t).
Proof. exact (MK_COMB (@lem4472549 A K k) (@lem4472550 A K t)). Qed.
Lemma lem4472553 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472554 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472553 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472555 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t) = (term529 A K k t).
Proof. exact (@lem4472554 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) t). Qed.
Lemma lem4472557 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term529 A K k t).
Proof. exact (TRANS (@lem4472551 A K k t) (@lem4472555 A K k t)). Qed.
Lemma lem4472558 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term530 A K k s) = (term531 A K k s).
Proof. exact (MK_COMB (@lem4472523 A K) (@lem4472540 A K k s)). Qed.
Lemma lem4472559 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term65 A K s k t) = (term532 A K s k t).
Proof. exact (MK_COMB (@lem4472558 A K k s) (@lem4472557 A K k t)). Qed.
Lemma lem4472561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472562 {A K : Type'} (f : type329 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> ((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472561 (type1223 A K) (type330 A K) f x). Qed.
Lemma lem4472563 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term531 A K k s) = (term533 A K k s).
Proof. exact (@lem4472562 A K (@SUBSET (prod K A)) (term529 A K k s)). Qed.
Lemma lem4472564 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term529 A K k t) = (term529 A K k t).
Proof. exact (eq_refl (term529 A K k t)). Qed.
Lemma lem4472565 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term532 A K s k t) = (term534 A K s k t).
Proof. exact (MK_COMB (@lem4472563 A K k s) (@lem4472564 A K k t)). Qed.
Lemma lem4472567 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472568 {A K : Type'} (f : type330 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472567 (type1223 A K) Prop f x). Qed.
Lemma lem4472569 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term534 A K s k t) = (term535 A K s k t).
Proof. exact (@lem4472568 A K (term533 A K k s) (term529 A K k t)). Qed.
Lemma lem4472570 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term532 A K s k t) = (term535 A K s k t).
Proof. exact (TRANS (@lem4472565 A K s k t) (@lem4472569 A K s k t)). Qed.
Lemma lem4472571 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term65 A K s k t) = (term535 A K s k t).
Proof. exact (TRANS (@lem4472559 A K s k t) (@lem4472570 A K s k t)). Qed.
Lemma lem4472572 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term536 A K s k t) = (term537 A K s k t).
Proof. exact (MK_COMB (@lem4472522) (@lem4472571 A K s k t)). Qed.
Lemma lem4472573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4472574 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term118 A K s k t) = (term538 A K s k t).
Proof. exact (MK_COMB (@lem4472573) (@lem4472572 A K s k t)). Qed.
Lemma lem4472575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term120 A K k s t) = (term539 A K k s t).
Proof. exact (MK_COMB (@lem4472574 A K s k t) (@lem4472521 A K k s t)). Qed.
Lemma lem4472576 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term141 A K k s) = (term540 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4472575 A K k s t)). Qed.
Lemma lem4472577 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472578 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term156 A K k s) = (term541 A K k s).
Proof. exact (MK_COMB (@lem4472577 A K) (@lem4472576 A K k s)). Qed.
Lemma lem4472579 {A K : Type'} (k : K -> Prop) : (term163 A K k) = (term542 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4472578 A K k s)). Qed.
Lemma lem4472580 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472581 {A K : Type'} (k : K -> Prop) : (term178 A K k) = (term543 A K k).
Proof. exact (MK_COMB (@lem4472580 A K) (@lem4472579 A K k)). Qed.
Lemma lem4472582 {A K : Type'} : (term187 A K) = (term544 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472581 A K k)). Qed.
Lemma lem4472583 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472584 {A K : Type'} : (term202 A K) = (term545 A K).
Proof. exact (MK_COMB (@lem4472583 K) (@lem4472582 A K)). Qed.
Lemma lem4472585 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4472586 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem4472587 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472597 {A K : Type'} (f : type843 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472596 (K -> Prop) (type732 A K) f x). Qed.
Lemma lem4472598 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (i' k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k).
Proof. exact (@lem4472597 A K i' k). Qed.
Lemma lem4472599 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472600 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s).
Proof. exact (MK_COMB (@lem4472598 A K i' k) (@lem4472599 A K s)). Qed.
Lemma lem4472602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472603 {A K : Type'} (f : type732 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472602 (type1470 A K) (type744 A K) f x). Qed.
Lemma lem4472604 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s) = (term546 A K i' k s).
Proof. exact (@lem4472603 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k) s). Qed.
Lemma lem4472605 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (term546 A K i' k s).
Proof. exact (TRANS (@lem4472600 A K i' k s) (@lem4472604 A K i' k s)). Qed.
Lemma lem4472606 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472607 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term547 A K i' k s t).
Proof. exact (MK_COMB (@lem4472605 A K i' k s) (@lem4472606 A K t)). Qed.
Lemma lem4472609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472610 {A K : Type'} (f : type744 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472609 (type1470 A K) K f x). Qed.
Lemma lem4472611 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term547 A K i' k s t) = (term548 A K i' k s t).
Proof. exact (@lem4472610 A K (term546 A K i' k s) t). Qed.
Lemma lem4472613 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term548 A K i' k s t).
Proof. exact (TRANS (@lem4472607 A K i' k s t) (@lem4472611 A K i' k s t)). Qed.
Lemma lem4472614 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K i' k s t) = (term550 A K i' k s t).
Proof. exact (MK_COMB (@lem4472587 A K s) (@lem4472613 A K i' k s t)). Qed.
Lemma lem4472616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472617 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472616 K (A -> Prop) f x). Qed.
Lemma lem4472618 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term550 A K i' k s t) = (term551 A K i' k s t).
Proof. exact (@lem4472617 A K s (term548 A K i' k s t)). Qed.
Lemma lem4472619 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term549 A K i' k s t) = (term551 A K i' k s t).
Proof. exact (TRANS (@lem4472614 A K i' k s t) (@lem4472618 A K i' k s t)). Qed.
Lemma lem4472620 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472630 {A K : Type'} (f : type843 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472629 (K -> Prop) (type732 A K) f x). Qed.
Lemma lem4472631 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (i' k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k).
Proof. exact (@lem4472630 A K i' k). Qed.
Lemma lem4472632 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472633 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s).
Proof. exact (MK_COMB (@lem4472631 A K i' k) (@lem4472632 A K s)). Qed.
Lemma lem4472635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472636 {A K : Type'} (f : type732 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472635 (type1470 A K) (type744 A K) f x). Qed.
Lemma lem4472637 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s) = (term546 A K i' k s).
Proof. exact (@lem4472636 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k) s). Qed.
Lemma lem4472638 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (term546 A K i' k s).
Proof. exact (TRANS (@lem4472633 A K i' k s) (@lem4472637 A K i' k s)). Qed.
Lemma lem4472639 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472640 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term547 A K i' k s t).
Proof. exact (MK_COMB (@lem4472638 A K i' k s) (@lem4472639 A K t)). Qed.
Lemma lem4472642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472643 {A K : Type'} (f : type744 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472642 (type1470 A K) K f x). Qed.
Lemma lem4472644 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term547 A K i' k s t) = (term548 A K i' k s t).
Proof. exact (@lem4472643 A K (term546 A K i' k s) t). Qed.
Lemma lem4472646 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term548 A K i' k s t).
Proof. exact (TRANS (@lem4472640 A K i' k s t) (@lem4472644 A K i' k s t)). Qed.
Lemma lem4472647 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term552 A K i' k s t) = (term553 A K i' k s t).
Proof. exact (MK_COMB (@lem4472620 A K t) (@lem4472646 A K i' k s t)). Qed.
Lemma lem4472649 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472650 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472649 K (A -> Prop) f x). Qed.
Lemma lem4472651 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term553 A K i' k s t) = (term554 A K i' k s t).
Proof. exact (@lem4472650 A K t (term548 A K i' k s t)). Qed.
Lemma lem4472652 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term552 A K i' k s t) = (term554 A K i' k s t).
Proof. exact (TRANS (@lem4472647 A K i' k s t) (@lem4472651 A K i' k s t)). Qed.
Lemma lem4472653 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term555 A K i' k s t) = (term556 A K i' k s t).
Proof. exact (MK_COMB (@lem4472586 A) (@lem4472619 A K i' k s t)). Qed.
Lemma lem4472654 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term557 A K i' k s t) = (term558 A K i' k s t).
Proof. exact (MK_COMB (@lem4472653 A K i' k s t) (@lem4472652 A K i' k s t)). Qed.
Lemma lem4472656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472657 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4472656 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4472658 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term556 A K i' k s t) = (term559 A K i' k s t).
Proof. exact (@lem4472657 A (@SUBSET A) (term551 A K i' k s t)). Qed.
Lemma lem4472659 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term554 A K i' k s t) = (term554 A K i' k s t).
Proof. exact (eq_refl (term554 A K i' k s t)). Qed.
Lemma lem4472660 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term558 A K i' k s t) = (term560 A K i' k s t).
Proof. exact (MK_COMB (@lem4472658 A K i' k s t) (@lem4472659 A K i' k s t)). Qed.
Lemma lem4472662 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472663 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4472662 (A -> Prop) Prop f x). Qed.
Lemma lem4472664 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term560 A K i' k s t) = (term561 A K i' k s t).
Proof. exact (@lem4472663 A (term559 A K i' k s t) (term554 A K i' k s t)). Qed.
Lemma lem4472665 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term558 A K i' k s t) = (term561 A K i' k s t).
Proof. exact (TRANS (@lem4472660 A K i' k s t) (@lem4472664 A K i' k s t)). Qed.
Lemma lem4472666 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term557 A K i' k s t) = (term561 A K i' k s t).
Proof. exact (TRANS (@lem4472654 A K i' k s t) (@lem4472665 A K i' k s t)). Qed.
Lemma lem4472667 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term562 A K i' k s t) = (term563 A K i' k s t).
Proof. exact (MK_COMB (@lem4472585) (@lem4472666 A K i' k s t)). Qed.
Lemma lem4472668 {K : Type'} : (@IN K) = (@IN K).
Proof. exact (eq_refl (@IN K)). Qed.
Lemma lem4472677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472678 {A K : Type'} (f : type843 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472677 (K -> Prop) (type732 A K) f x). Qed.
Lemma lem4472679 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (i' k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k).
Proof. exact (@lem4472678 A K i' k). Qed.
Lemma lem4472680 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472681 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s).
Proof. exact (MK_COMB (@lem4472679 A K i' k) (@lem4472680 A K s)). Qed.
Lemma lem4472683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472684 {A K : Type'} (f : type732 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472683 (type1470 A K) (type744 A K) f x). Qed.
Lemma lem4472685 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k s) = (term546 A K i' k s).
Proof. exact (@lem4472684 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (K -> A -> Prop) -> K) i' k) s). Qed.
Lemma lem4472686 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (i' k s) = (term546 A K i' k s).
Proof. exact (TRANS (@lem4472681 A K i' k s) (@lem4472685 A K i' k s)). Qed.
Lemma lem4472687 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472688 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term547 A K i' k s t).
Proof. exact (MK_COMB (@lem4472686 A K i' k s) (@lem4472687 A K t)). Qed.
Lemma lem4472690 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472691 {A K : Type'} (f : type744 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> K) f x).
Proof. exact (@lem4472690 (type1470 A K) K f x). Qed.
Lemma lem4472692 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term547 A K i' k s t) = (term548 A K i' k s t).
Proof. exact (@lem4472691 A K (term546 A K i' k s) t). Qed.
Lemma lem4472694 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (i' k s t) = (term548 A K i' k s t).
Proof. exact (TRANS (@lem4472688 A K i' k s t) (@lem4472692 A K i' k s t)). Qed.
Lemma lem4472695 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4472696 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term564 A K i' k s t) = (term565 A K i' k s t).
Proof. exact (MK_COMB (@lem4472668 K) (@lem4472694 A K i' k s t)). Qed.
Lemma lem4472697 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term566 A K i' s t k) = (term567 A K i' s t k).
Proof. exact (MK_COMB (@lem4472696 A K i' k s t) (@lem4472695 K k)). Qed.
Lemma lem4472699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472700 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4472699 K (type686 K) f x). Qed.
Lemma lem4472701 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term565 A K i' k s t) = (term568 A K i' k s t).
Proof. exact (@lem4472700 K (@IN K) (term548 A K i' k s t)). Qed.
Lemma lem4472702 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4472703 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term567 A K i' s t k) = (term569 A K i' s t k).
Proof. exact (MK_COMB (@lem4472701 A K i' k s t) (@lem4472702 K k)). Qed.
Lemma lem4472705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472706 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4472705 (K -> Prop) Prop f x). Qed.
Lemma lem4472707 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term569 A K i' s t k) = (term570 A K i' s t k).
Proof. exact (@lem4472706 K (term568 A K i' k s t) k). Qed.
Lemma lem4472708 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term567 A K i' s t k) = (term570 A K i' s t k).
Proof. exact (TRANS (@lem4472703 A K i' s t k) (@lem4472707 A K i' s t k)). Qed.
Lemma lem4472709 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term566 A K i' s t k) = (term570 A K i' s t k).
Proof. exact (TRANS (@lem4472697 A K i' s t k) (@lem4472708 A K i' s t k)). Qed.
Lemma lem4472710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472711 {A K : Type'} (i' : type843 A K) (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : (term571 A K i' s t k) = (term572 A K i' s t k).
Proof. exact (MK_COMB (@lem4472710) (@lem4472709 A K i' s t k)). Qed.
Lemma lem4472712 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term573 A K i' k s t) = (term574 A K i' k s t).
Proof. exact (MK_COMB (@lem4472711 A K i' s t k) (@lem4472667 A K i' k s t)). Qed.
Lemma lem4472713 {A K : Type'} : (@SUBSET (prod K A)) = (@SUBSET (prod K A)).
Proof. exact (eq_refl (@SUBSET (prod K A))). Qed.
Lemma lem4472720 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472721 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472720 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472722 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472721 A K (@disjoint_union A K) k). Qed.
Lemma lem4472723 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472724 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s).
Proof. exact (MK_COMB (@lem4472722 A K k) (@lem4472723 A K s)). Qed.
Lemma lem4472726 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472727 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472726 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s) = (term529 A K k s).
Proof. exact (@lem4472727 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) s). Qed.
Lemma lem4472730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term529 A K k s).
Proof. exact (TRANS (@lem4472724 A K k s) (@lem4472728 A K k s)). Qed.
Lemma lem4472737 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472738 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472737 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472739 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472738 A K (@disjoint_union A K) k). Qed.
Lemma lem4472740 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472741 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t).
Proof. exact (MK_COMB (@lem4472739 A K k) (@lem4472740 A K t)). Qed.
Lemma lem4472743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472744 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472743 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472745 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t) = (term529 A K k t).
Proof. exact (@lem4472744 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) t). Qed.
Lemma lem4472747 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term529 A K k t).
Proof. exact (TRANS (@lem4472741 A K k t) (@lem4472745 A K k t)). Qed.
Lemma lem4472748 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term530 A K k s) = (term531 A K k s).
Proof. exact (MK_COMB (@lem4472713 A K) (@lem4472730 A K k s)). Qed.
Lemma lem4472749 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term65 A K s k t) = (term532 A K s k t).
Proof. exact (MK_COMB (@lem4472748 A K k s) (@lem4472747 A K k t)). Qed.
Lemma lem4472751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472752 {A K : Type'} (f : type329 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> ((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472751 (type1223 A K) (type330 A K) f x). Qed.
Lemma lem4472753 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term531 A K k s) = (term533 A K k s).
Proof. exact (@lem4472752 A K (@SUBSET (prod K A)) (term529 A K k s)). Qed.
Lemma lem4472754 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term529 A K k t) = (term529 A K k t).
Proof. exact (eq_refl (term529 A K k t)). Qed.
Lemma lem4472755 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term532 A K s k t) = (term534 A K s k t).
Proof. exact (MK_COMB (@lem4472753 A K k s) (@lem4472754 A K k t)). Qed.
Lemma lem4472757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472758 {A K : Type'} (f : type330 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472757 (type1223 A K) Prop f x). Qed.
Lemma lem4472759 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term534 A K s k t) = (term535 A K s k t).
Proof. exact (@lem4472758 A K (term533 A K k s) (term529 A K k t)). Qed.
Lemma lem4472760 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term532 A K s k t) = (term535 A K s k t).
Proof. exact (TRANS (@lem4472755 A K s k t) (@lem4472759 A K s k t)). Qed.
Lemma lem4472761 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term65 A K s k t) = (term535 A K s k t).
Proof. exact (TRANS (@lem4472749 A K s k t) (@lem4472760 A K s k t)). Qed.
Lemma lem4472762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4472763 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term121 A K s k t) = (term575 A K s k t).
Proof. exact (MK_COMB (@lem4472762) (@lem4472761 A K s k t)). Qed.
Lemma lem4472764 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term576 A K i' k s t) = (term577 A K i' k s t).
Proof. exact (MK_COMB (@lem4472763 A K s k t) (@lem4472712 A K i' k s t)). Qed.
Lemma lem4472765 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (term578 A K i' k s) = (term579 A K i' k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4472764 A K i' k s t)). Qed.
Lemma lem4472766 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472767 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (term580 A K i' k s) = (term581 A K i' k s).
Proof. exact (MK_COMB (@lem4472766 A K) (@lem4472765 A K i' k s)). Qed.
Lemma lem4472768 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (term582 A K i' k) = (term583 A K i' k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4472767 A K i' k s)). Qed.
Lemma lem4472769 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472770 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (term287 A K i' k) = (term584 A K i' k).
Proof. exact (MK_COMB (@lem4472769 A K) (@lem4472768 A K i' k)). Qed.
Lemma lem4472771 {A K : Type'} (i' : type843 A K) : (term289 A K i') = (term585 A K i').
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472770 A K i' k)). Qed.
Lemma lem4472772 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472773 {A K : Type'} (i' : type843 A K) : (term291 A K i') = (term586 A K i').
Proof. exact (MK_COMB (@lem4472772 K) (@lem4472771 A K i')). Qed.
Lemma lem4472774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472775 {A K : Type'} (i' : type843 A K) : (term308 A K i') = (term587 A K i').
Proof. exact (MK_COMB (@lem4472774) (@lem4472773 A K i')). Qed.
Lemma lem4472776 {A K : Type'} (i' : type843 A K) : (term310 A K i') = (term588 A K i').
Proof. exact (MK_COMB (@lem4472775 A K i') (@lem4472584 A K)). Qed.
Lemma lem4472777 {A K : Type'} (i' : type843 A K) (h1 : term310 A K i') : term588 A K i'.
Proof. exact (EQ_MP (@lem4472776 A K i') (@lem4472152 A K i' h1)). Qed.
Lemma lem4472778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4472787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472788 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472787 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472789 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472788 A K (@disjoint_union A K) k). Qed.
Lemma lem4472790 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4472791 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s).
Proof. exact (MK_COMB (@lem4472789 A K k) (@lem4472790 A K s)). Qed.
Lemma lem4472793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472794 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472793 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472795 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k s) = (term529 A K k s).
Proof. exact (@lem4472794 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) s). Qed.
Lemma lem4472797 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term529 A K k s).
Proof. exact (TRANS (@lem4472791 A K k s) (@lem4472795 A K k s)). Qed.
Lemma lem4472798 {A K : Type'} (u : type1223 A K) : (@SUBSET (prod K A) u) = (@SUBSET (prod K A) u).
Proof. exact (eq_refl (@SUBSET (prod K A) u)). Qed.
Lemma lem4472799 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term21 A K u k s) = (term589 A K u k s).
Proof. exact (MK_COMB (@lem4472798 A K u) (@lem4472797 A K k s)). Qed.
Lemma lem4472801 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472802 {A K : Type'} (f : type329 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> ((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472801 (type1223 A K) (type330 A K) f x). Qed.
Lemma lem4472803 {A K : Type'} (u : type1223 A K) : (@SUBSET (prod K A) u) = (@I (((prod K A) -> Prop) -> ((prod K A) -> Prop) -> Prop) (@SUBSET (prod K A)) u).
Proof. exact (@lem4472802 A K (@SUBSET (prod K A)) u). Qed.
Lemma lem4472804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term529 A K k s) = (term529 A K k s).
Proof. exact (eq_refl (term529 A K k s)). Qed.
Lemma lem4472805 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term589 A K u k s) = (term590 A K u k s).
Proof. exact (MK_COMB (@lem4472803 A K u) (@lem4472804 A K k s)). Qed.
Lemma lem4472807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472808 {A K : Type'} (f : type330 A K) (x : type1223 A K) : (f x) = (@I (((prod K A) -> Prop) -> Prop) f x).
Proof. exact (@lem4472807 (type1223 A K) Prop f x). Qed.
Lemma lem4472809 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term590 A K u k s) = (term591 A K u k s).
Proof. exact (@lem4472808 A K (@I (((prod K A) -> Prop) -> ((prod K A) -> Prop) -> Prop) (@SUBSET (prod K A)) u) (term529 A K k s)). Qed.
Lemma lem4472810 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term589 A K u k s) = (term591 A K u k s).
Proof. exact (TRANS (@lem4472805 A K u k s) (@lem4472809 A K u k s)). Qed.
Lemma lem4472811 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term21 A K u k s) = (term591 A K u k s).
Proof. exact (TRANS (@lem4472799 A K u k s) (@lem4472810 A K u k s)). Qed.
Lemma lem4472812 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term83 A K u k s) = (term592 A K u k s).
Proof. exact (MK_COMB (@lem4472778) (@lem4472811 A K u k s)). Qed.
Lemma lem4472813 {A : Type'} : (@SUBSET A) = (@SUBSET A).
Proof. exact (eq_refl (@SUBSET A)). Qed.
Lemma lem4472818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472819 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472818 K (A -> Prop) f x). Qed.
Lemma lem4472821 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4472819 A K t i). Qed.
Lemma lem4472826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472827 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4472826 K (A -> Prop) f x). Qed.
Lemma lem4472829 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4472827 A K s i). Qed.
Lemma lem4472830 {A K : Type'} (t : type1470 A K) (i : K) : (term515 A K t i) = (term516 A K t i).
Proof. exact (MK_COMB (@lem4472813 A) (@lem4472821 A K t i)). Qed.
Lemma lem4472831 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term77 A K t s i) = (term517 A K t s i).
Proof. exact (MK_COMB (@lem4472830 A K t i) (@lem4472829 A K s i)). Qed.
Lemma lem4472833 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472834 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4472833 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4472835 {A K : Type'} (t : type1470 A K) (i : K) : (term516 A K t i) = (term518 A K t i).
Proof. exact (@lem4472834 A (@SUBSET A) (@I (K -> A -> Prop) t i)). Qed.
Lemma lem4472836 {A K : Type'} (s : type1470 A K) (i : K) : (@I (K -> A -> Prop) s i) = (@I (K -> A -> Prop) s i).
Proof. exact (eq_refl (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4472837 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term517 A K t s i) = (term519 A K t s i).
Proof. exact (MK_COMB (@lem4472835 A K t i) (@lem4472836 A K s i)). Qed.
Lemma lem4472839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472840 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4472839 (A -> Prop) Prop f x). Qed.
Lemma lem4472841 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term519 A K t s i) = (term520 A K t s i).
Proof. exact (@lem4472840 A (term518 A K t i) (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4472842 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term517 A K t s i) = (term520 A K t s i).
Proof. exact (TRANS (@lem4472837 A K t s i) (@lem4472841 A K t s i)). Qed.
Lemma lem4472843 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term77 A K t s i) = (term520 A K t s i).
Proof. exact (TRANS (@lem4472831 A K t s i) (@lem4472842 A K t s i)). Qed.
Lemma lem4472844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4472851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472852 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4472851 K (type686 K) f x). Qed.
Lemma lem4472853 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4472852 K (@IN K) i). Qed.
Lemma lem4472854 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4472855 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4472853 K i) (@lem4472854 K k)). Qed.
Lemma lem4472857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472858 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4472857 (K -> Prop) Prop f x). Qed.
Lemma lem4472859 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term521 K i k).
Proof. exact (@lem4472858 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4472861 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term521 K i k).
Proof. exact (TRANS (@lem4472855 K i k) (@lem4472859 K i k)). Qed.
Lemma lem4472862 {K : Type'} (i : K) (k : K -> Prop) : (term522 K i k) = (term523 K i k).
Proof. exact (MK_COMB (@lem4472844) (@lem4472861 K i k)). Qed.
Lemma lem4472863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4472864 {K : Type'} (i : K) (k : K -> Prop) : (term524 K i k) = (term525 K i k).
Proof. exact (MK_COMB (@lem4472863) (@lem4472862 K i k)). Qed.
Lemma lem4472865 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term76 A K k t s i) = (term526 A K k t s i).
Proof. exact (MK_COMB (@lem4472864 K i k) (@lem4472843 A K t s i)). Qed.
Lemma lem4472866 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term78 A K k t s) = (term527 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4472865 A K k t s i)). Qed.
Lemma lem4472867 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4472868 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term79 A K k t s) = (term528 A K k t s).
Proof. exact (MK_COMB (@lem4472867 K) (@lem4472866 A K k t s)). Qed.
Lemma lem4472877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472878 {A K : Type'} (f : type846 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472877 (K -> Prop) (type737 A K) f x). Qed.
Lemma lem4472879 {A K : Type'} (k : K -> Prop) : (@disjoint_union A K k) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k).
Proof. exact (@lem4472878 A K (@disjoint_union A K) k). Qed.
Lemma lem4472880 {A K : Type'} (t : type1470 A K) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4472881 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t).
Proof. exact (MK_COMB (@lem4472879 A K k) (@lem4472880 A K t)). Qed.
Lemma lem4472883 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4472884 {A K : Type'} (f : type737 A K) (x : type1470 A K) : (f x) = (@I ((K -> A -> Prop) -> (prod K A) -> Prop) f x).
Proof. exact (@lem4472883 (type1470 A K) (type1223 A K) f x). Qed.
Lemma lem4472885 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k t) = (term529 A K k t).
Proof. exact (@lem4472884 A K (@I ((K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop) (@disjoint_union A K) k) t). Qed.
Lemma lem4472887 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term529 A K k t).
Proof. exact (TRANS (@lem4472881 A K k t) (@lem4472885 A K k t)). Qed.
Lemma lem4472888 {A K : Type'} (u : type1223 A K) : (@eq ((prod K A) -> Prop) u) = (@eq ((prod K A) -> Prop) u).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop) u)). Qed.
Lemma lem4472889 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) : (u = (@disjoint_union A K k t)) = (u = (term529 A K k t)).
Proof. exact (MK_COMB (@lem4472888 A K u) (@lem4472887 A K k t)). Qed.
Lemma lem4472890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472891 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) : (term71 A K u k t) = (term593 A K u k t).
Proof. exact (MK_COMB (@lem4472890) (@lem4472889 A K u k t)). Qed.
Lemma lem4472892 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term80 A K u k t s) = (term594 A K u k t s).
Proof. exact (MK_COMB (@lem4472891 A K u k t) (@lem4472868 A K k t s)). Qed.
Lemma lem4472893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4472894 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term101 A K u k t s) = (term595 A K u k t s).
Proof. exact (MK_COMB (@lem4472893) (@lem4472892 A K u k t s)). Qed.
Lemma lem4472895 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term103 A K t u k s) = (term596 A K t u k s).
Proof. exact (MK_COMB (@lem4472894 A K u k t s) (@lem4472812 A K u k s)). Qed.
Lemma lem4472896 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term596 A K t u k s.
Proof. exact (EQ_MP (@lem4472895 A K t u k s) (@lem4472153 A K t u k s h1)). Qed.
Lemma lem4472898 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term594 A K u k t s.
Proof. exact (proj1 (@lem4472896 A K t u k s h1)). Qed.
Lemma lem4472899 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term528 A K k t s.
Proof. exact (proj2 (@lem4472898 A K t u k s h1)). Qed.
Lemma lem4472902 {A K : Type'} (i' : type843 A K) (h1 : term310 A K i') : term586 A K i'.
Proof. exact (proj1 (@lem4472777 A K i' h1)). Qed.
Lemma lem4472920 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term526 A K k t s i) = (term526 A K k t s i).
Proof. exact (eq_refl (term526 A K k t s i)). Qed.
Lemma lem4472921 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term527 A K k t s) = (term527 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4472920 A K k t s i)). Qed.
Lemma lem4472922 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4472924 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term528 A K k t s) = (term528 A K k t s).
Proof. exact (MK_COMB (@lem4472922 K) (@lem4472921 A K k t s)). Qed.
Lemma lem4472925 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term528 A K k t s.
Proof. exact (EQ_MP (@lem4472924 A K k t s) (@lem4472899 A K t u k s h1)). Qed.
Lemma lem4472943 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term577 A K i' k s t) = (term597 A K i' k s t).
Proof. exact (@lem19490 (term570 A K i' s t k) (term535 A K s k t) (term563 A K i' k s t)). Qed.
Lemma lem4472944 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (term579 A K i' k s) = (term598 A K i' k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4472943 A K i' k s t)). Qed.
Lemma lem4472945 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472946 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (s : type1470 A K) : (term581 A K i' k s) = (term599 A K i' k s).
Proof. exact (MK_COMB (@lem4472945 A K) (@lem4472944 A K i' k s)). Qed.
Lemma lem4472947 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (term583 A K i' k) = (term600 A K i' k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4472946 A K i' k s)). Qed.
Lemma lem4472948 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4472949 {A K : Type'} (i' : type843 A K) (k : K -> Prop) : (term584 A K i' k) = (term601 A K i' k).
Proof. exact (MK_COMB (@lem4472948 A K) (@lem4472947 A K i' k)). Qed.
Lemma lem4472950 {A K : Type'} (i' : type843 A K) : (term585 A K i') = (term602 A K i').
Proof. exact (fun_ext (fun k : K -> Prop => @lem4472949 A K i' k)). Qed.
Lemma lem4472951 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4472953 {A K : Type'} (i' : type843 A K) : (term586 A K i') = (term603 A K i').
Proof. exact (MK_COMB (@lem4472951 K) (@lem4472950 A K i')). Qed.
Lemma lem4472954 {A K : Type'} (i' : type843 A K) (h1 : term310 A K i') : term603 A K i'.
Proof. exact (EQ_MP (@lem4472953 A K i') (@lem4472902 A K i' h1)). Qed.
Lemma lem4473096 {A K : Type'} (_51692 : K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term604 A K k t s _51692.
Proof. exact (@lem4472925 A K t u k s h1 _51692). Qed.
Lemma lem4473097 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51692 : K) : (term604 A K k t s _51692) = (term526 A K k t s _51692).
Proof. exact (eq_refl (term604 A K k t s _51692)). Qed.
Lemma lem4473099 {A K : Type'} (_51693 : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term605 A K i' _51693.
Proof. exact (@lem4472954 A K i' h1 _51693). Qed.
Lemma lem4473100 {A K : Type'} (i' : type843 A K) (_51693 : K -> Prop) : (term605 A K i' _51693) = (term601 A K i' _51693).
Proof. exact (eq_refl (term605 A K i' _51693)). Qed.
Lemma lem4473101 {A K : Type'} (_51693 : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term601 A K i' _51693.
Proof. exact (EQ_MP (@lem4473100 A K i' _51693) (@lem4473099 A K _51693 i' h1)). Qed.
Lemma lem4473102 {A K : Type'} (_51693 : K -> Prop) (_51694 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term606 A K i' _51693 _51694.
Proof. exact (@lem4473101 A K _51693 i' h1 _51694). Qed.
Lemma lem4473103 {A K : Type'} (i' : type843 A K) (_51693 : K -> Prop) (_51694 : type1470 A K) : (term606 A K i' _51693 _51694) = (term599 A K i' _51693 _51694).
Proof. exact (eq_refl (term606 A K i' _51693 _51694)). Qed.
Lemma lem4473104 {A K : Type'} (_51693 : K -> Prop) (_51694 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term599 A K i' _51693 _51694.
Proof. exact (EQ_MP (@lem4473103 A K i' _51693 _51694) (@lem4473102 A K _51693 _51694 i' h1)). Qed.
Lemma lem4473105 {A K : Type'} (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term607 A K i' _51693 _51694 _51695.
Proof. exact (@lem4473104 A K _51693 _51694 i' h1 _51695). Qed.
Lemma lem4473106 {A K : Type'} (i' : type843 A K) (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) : (term607 A K i' _51693 _51694 _51695) = (term597 A K i' _51693 _51694 _51695).
Proof. exact (eq_refl (term607 A K i' _51693 _51694 _51695)). Qed.
Lemma lem4473107 {A K : Type'} (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term597 A K i' _51693 _51694 _51695.
Proof. exact (EQ_MP (@lem4473106 A K i' _51693 _51694 _51695) (@lem4473105 A K _51693 _51694 _51695 i' h1)). Qed.
Lemma lem4473146 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term592 A K u k s.
Proof. exact (proj2 (@lem4472896 A K t u k s h1)). Qed.
Lemma lem4473148 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : u = (term529 A K k t).
Proof. exact (proj1 (@lem4472898 A K t u k s h1)). Qed.
Lemma lem4473213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term608 A K k s) = (term608 A K k s).
Proof. exact (eq_refl (term608 A K k s)). Qed.
Lemma lem4473214 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : (term609 A K k s u) = (term610 A K s k t).
Proof. exact (MK_COMB (@lem4473213 A K k s) (@lem4473148 A K t u k s h1)). Qed.
Lemma lem4473215 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : (term610 A K s k t) = (term537 A K t k s).
Proof. exact (eq_refl (term610 A K s k t)). Qed.
Lemma lem4473216 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (u : type1223 A K) : (term611 A K k s u) = (term611 A K k s u).
Proof. exact (eq_refl (term611 A K k s u)). Qed.
Lemma lem4473217 {A K : Type'} (u : type1223 A K) (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : ((term609 A K k s u) = (term610 A K s k t)) = ((term609 A K k s u) = (term537 A K t k s)).
Proof. exact (MK_COMB (@lem4473216 A K k s u) (@lem4473215 A K t k s)). Qed.
Lemma lem4473218 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term609 A K k s u) = (term592 A K u k s).
Proof. exact (eq_refl (term609 A K k s u)). Qed.
Lemma lem4473219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473220 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term611 A K k s u) = (term612 A K u k s).
Proof. exact (MK_COMB (@lem4473219) (@lem4473218 A K u k s)). Qed.
Lemma lem4473221 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : (term537 A K t k s) = (term537 A K t k s).
Proof. exact (eq_refl (term537 A K t k s)). Qed.
Lemma lem4473222 {A K : Type'} (u : type1223 A K) (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : ((term609 A K k s u) = (term537 A K t k s)) = ((term592 A K u k s) = (term537 A K t k s)).
Proof. exact (MK_COMB (@lem4473220 A K u k s) (@lem4473221 A K t k s)). Qed.
Lemma lem4473223 {A K : Type'} (u : type1223 A K) (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : ((term609 A K k s u) = (term610 A K s k t)) = ((term592 A K u k s) = (term537 A K t k s)).
Proof. exact (TRANS (@lem4473217 A K u t k s) (@lem4473222 A K u t k s)). Qed.
Lemma lem4473224 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : (term592 A K u k s) = (term537 A K t k s).
Proof. exact (EQ_MP (@lem4473223 A K u t k s) (@lem4473214 A K t u k s h1)). Qed.
Lemma lem4473225 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term537 A K t k s.
Proof. exact (EQ_MP (@lem4473224 A K t u k s h1) (@lem4473146 A K t u k s h1)). Qed.
Lemma lem4473239 {A K : Type'} (_51692 : K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term526 A K k t s _51692.
Proof. exact (EQ_MP (@lem4473097 A K k t s _51692) (@lem4473096 A K _51692 t u k s h1)). Qed.
Lemma lem4473309 {A K : Type'} (_51694 : type1470 A K) (_51695 : type1470 A K) (_51693 : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term613 A K i' _51694 _51695 _51693.
Proof. exact (proj1 (@lem4473107 A K _51693 _51694 _51695 i' h1)). Qed.
Lemma lem4473323 {A K : Type'} (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term614 A K i' _51693 _51694 _51695.
Proof. exact (proj2 (@lem4473107 A K _51693 _51694 _51695 i' h1)). Qed.
Lemma lem4473326 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) : term537 A K t k s.
Proof. exact (h1). Qed.
Lemma lem4473327 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) : term615 A K t k s.
Proof. exact (fun h0 : term535 A K t k s => @lem4473326 A K t k s h1). Qed.
Lemma lem4473329 (p : Prop) : (term616 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4473330 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : (term615 A K t k s) = (term537 A K t k s).
Proof. exact (@lem4473329 (term535 A K t k s)). Qed.
Lemma lem4473331 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) : term537 A K t k s.
Proof. exact (EQ_MP (@lem4473330 A K t k s) (@lem4473327 A K t k s h1)). Qed.
Lemma lem4473337 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4473338 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term613 A K i' _51694 _51695 _51693) = (term617 A K i' _51694 _51693 _51695).
Proof. exact (@lem4473337 (term570 A K i' _51694 _51695 _51693) (term535 A K _51694 _51693 _51695)). Qed.
Lemma lem4473344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473345 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term618 A K i' _51694 _51695 _51693) = (term619 A K i' _51694 _51693 _51695).
Proof. exact (MK_COMB (@lem4473344) (@lem4473338 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473351 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term617 A K i' _51694 _51693 _51695) = (term617 A K i' _51694 _51693 _51695).
Proof. exact (eq_refl (term617 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473352 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : ((term613 A K i' _51694 _51695 _51693) = (term617 A K i' _51694 _51693 _51695)) = ((term617 A K i' _51694 _51693 _51695) = (term617 A K i' _51694 _51693 _51695)).
Proof. exact (MK_COMB (@lem4473345 A K i' _51694 _51693 _51695) (@lem4473351 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4473355 (x : Prop) : (x = x) = True.
Proof. exact (@lem4473354 Prop x). Qed.
Lemma lem4473356 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : ((term617 A K i' _51694 _51693 _51695) = (term617 A K i' _51694 _51693 _51695)) = True.
Proof. exact (@lem4473355 (term617 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473357 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : ((term613 A K i' _51694 _51695 _51693) = (term617 A K i' _51694 _51693 _51695)) = True.
Proof. exact (TRANS (@lem4473352 A K i' _51694 _51693 _51695) (@lem4473356 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473358 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : True = ((term613 A K i' _51694 _51695 _51693) = (term617 A K i' _51694 _51693 _51695)).
Proof. exact (SYM (@lem4473357 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473359 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term613 A K i' _51694 _51695 _51693) = (term617 A K i' _51694 _51693 _51695).
Proof. exact (EQ_MP (@lem4473358 A K i' _51694 _51693 _51695) (@lem0)). Qed.
Lemma lem4473360 {A K : Type'} (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term617 A K i' _51694 _51693 _51695.
Proof. exact (EQ_MP (@lem4473359 A K i' _51694 _51693 _51695) (@lem4473309 A K _51694 _51695 _51693 i' h1)). Qed.
Lemma lem4473362 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4473365 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51695 : type1470 A K) (_51693 : K -> Prop) : (term617 A K i' _51694 _51693 _51695) = (term621 A K i' _51694 _51695 _51693).
Proof. exact (@lem4473362 (term535 A K _51694 _51693 _51695) (term570 A K i' _51694 _51695 _51693)). Qed.
Lemma lem4473368 {A K : Type'} (_51694 : type1470 A K) (_51695 : type1470 A K) (_51693 : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term621 A K i' _51694 _51695 _51693.
Proof. exact (EQ_MP (@lem4473365 A K i' _51694 _51695 _51693) (@lem4473360 A K _51694 _51693 _51695 i' h1)). Qed.
Lemma lem4473369 {A K : Type'} (_51694 : type1470 A K) (_51695 : type1470 A K) (_51693 : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term621 A K i' _51694 _51695 _51693.
Proof. exact (@lem4473368 A K _51694 _51695 _51693 i' h1). Qed.
Lemma lem4473370 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (k : K -> Prop) (i' : type843 A K) (h1 : term310 A K i') : term621 A K i' t s k.
Proof. exact (@lem4473369 A K t s k i' h1). Qed.
Lemma lem4473373 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (i' : type843 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') : term570 A K i' t s k.
Proof. exact (@lem4473370 A K t s k i' h2 (@lem4473331 A K t k s h1)). Qed.
Lemma lem4473374 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (i' : type843 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') : term622 A K i' t s k.
Proof. exact (fun h0 : term623 A K i' t s k => @lem4473373 A K t k s i' h1 h2). Qed.
Lemma lem4473376 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4473377 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (s : type1470 A K) (k : K -> Prop) : (term622 A K i' t s k) = (term570 A K i' t s k).
Proof. exact (@lem4473376 (term570 A K i' t s k)). Qed.
Lemma lem4473378 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (i' : type843 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') : term570 A K i' t s k.
Proof. exact (EQ_MP (@lem4473377 A K i' t s k) (@lem4473374 A K t k s i' h1 h2)). Qed.
Lemma lem4473384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4473385 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : (term526 A K k t s _51692) = (term625 A K t s _51692 k).
Proof. exact (@lem4473384 (term520 A K t s _51692) (term523 K _51692 k)). Qed.
Lemma lem4473391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473392 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : (term626 A K k t s _51692) = (term627 A K t s _51692 k).
Proof. exact (MK_COMB (@lem4473391) (@lem4473385 A K t s _51692 k)). Qed.
Lemma lem4473398 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : (term625 A K t s _51692 k) = (term625 A K t s _51692 k).
Proof. exact (eq_refl (term625 A K t s _51692 k)). Qed.
Lemma lem4473399 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : ((term526 A K k t s _51692) = (term625 A K t s _51692 k)) = ((term625 A K t s _51692 k) = (term625 A K t s _51692 k)).
Proof. exact (MK_COMB (@lem4473392 A K t s _51692 k) (@lem4473398 A K t s _51692 k)). Qed.
Lemma lem4473401 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4473402 (x : Prop) : (x = x) = True.
Proof. exact (@lem4473401 Prop x). Qed.
Lemma lem4473403 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : ((term625 A K t s _51692 k) = (term625 A K t s _51692 k)) = True.
Proof. exact (@lem4473402 (term625 A K t s _51692 k)). Qed.
Lemma lem4473404 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : ((term526 A K k t s _51692) = (term625 A K t s _51692 k)) = True.
Proof. exact (TRANS (@lem4473399 A K t s _51692 k) (@lem4473403 A K t s _51692 k)). Qed.
Lemma lem4473405 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : True = ((term526 A K k t s _51692) = (term625 A K t s _51692 k)).
Proof. exact (SYM (@lem4473404 A K t s _51692 k)). Qed.
Lemma lem4473406 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) (k : K -> Prop) : (term526 A K k t s _51692) = (term625 A K t s _51692 k).
Proof. exact (EQ_MP (@lem4473405 A K t s _51692 k) (@lem0)). Qed.
Lemma lem4473407 {A K : Type'} (_51692 : K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term625 A K t s _51692 k.
Proof. exact (EQ_MP (@lem4473406 A K t s _51692 k) (@lem4473239 A K _51692 t u k s h1)). Qed.
Lemma lem4473409 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4473410 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51692 : K) : (term625 A K t s _51692 k) = (term628 A K k t s _51692).
Proof. exact (@lem4473409 (term523 K _51692 k) (term520 A K t s _51692)). Qed.
Lemma lem4473412 (a : Prop) : (term629 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4473413 {K : Type'} (_51692 : K) (k : K -> Prop) : (term630 K _51692 k) = (term521 K _51692 k).
Proof. exact (@lem4473412 (term521 K _51692 k)). Qed.
Lemma lem4473414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473415 {K : Type'} (_51692 : K) (k : K -> Prop) : (term631 K _51692 k) = (term632 K _51692 k).
Proof. exact (MK_COMB (@lem4473414) (@lem4473413 K _51692 k)). Qed.
Lemma lem4473416 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51692 : K) : (term520 A K t s _51692) = (term520 A K t s _51692).
Proof. exact (eq_refl (term520 A K t s _51692)). Qed.
Lemma lem4473417 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51692 : K) : (term628 A K k t s _51692) = (term633 A K k t s _51692).
Proof. exact (MK_COMB (@lem4473415 K _51692 k) (@lem4473416 A K t s _51692)). Qed.
Lemma lem4473418 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51692 : K) : (term625 A K t s _51692 k) = (term633 A K k t s _51692).
Proof. exact (TRANS (@lem4473410 A K k t s _51692) (@lem4473417 A K k t s _51692)). Qed.
Lemma lem4473421 {A K : Type'} (_51692 : K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term633 A K k t s _51692.
Proof. exact (EQ_MP (@lem4473418 A K k t s _51692) (@lem4473407 A K _51692 t u k s h1)). Qed.
Lemma lem4473422 {A K : Type'} (_51692 : K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term633 A K k t s _51692.
Proof. exact (@lem4473421 A K _51692 t u k s h1). Qed.
Lemma lem4473423 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term634 A K i' k t s.
Proof. exact (@lem4473422 A K (term548 A K i' k t s) t u k s h1). Qed.
Lemma lem4473426 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') (h3 : term103 A K t u k s) : term561 A K i' k t s.
Proof. exact (@lem4473423 A K i' t u k s h3 (@lem4473378 A K t k s i' h1 h2)). Qed.
Lemma lem4473427 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') (h3 : term103 A K t u k s) : term635 A K i' k t s.
Proof. exact (fun h0 : term563 A K i' k t s => @lem4473426 A K i' t u k s h1 h2 h3). Qed.
Lemma lem4473429 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4473430 {A K : Type'} (i' : type843 A K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term635 A K i' k t s) = (term561 A K i' k t s).
Proof. exact (@lem4473429 (term561 A K i' k t s)). Qed.
Lemma lem4473431 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') (h3 : term103 A K t u k s) : term561 A K i' k t s.
Proof. exact (EQ_MP (@lem4473430 A K i' k t s) (@lem4473427 A K i' t u k s h1 h2 h3)). Qed.
Lemma lem4473433 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4473434 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term614 A K i' _51693 _51694 _51695) = (term636 A K i' _51694 _51693 _51695).
Proof. exact (@lem4473433 (term563 A K i' _51693 _51694 _51695) (term535 A K _51694 _51693 _51695)). Qed.
Lemma lem4473436 (a : Prop) : (term629 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4473437 {A K : Type'} (i' : type843 A K) (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) : (term637 A K i' _51693 _51694 _51695) = (term561 A K i' _51693 _51694 _51695).
Proof. exact (@lem4473436 (term561 A K i' _51693 _51694 _51695)). Qed.
Lemma lem4473438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473439 {A K : Type'} (i' : type843 A K) (_51693 : K -> Prop) (_51694 : type1470 A K) (_51695 : type1470 A K) : (term638 A K i' _51693 _51694 _51695) = (term639 A K i' _51693 _51694 _51695).
Proof. exact (MK_COMB (@lem4473438) (@lem4473437 A K i' _51693 _51694 _51695)). Qed.
Lemma lem4473440 {A K : Type'} (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term535 A K _51694 _51693 _51695) = (term535 A K _51694 _51693 _51695).
Proof. exact (eq_refl (term535 A K _51694 _51693 _51695)). Qed.
Lemma lem4473441 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term636 A K i' _51694 _51693 _51695) = (term640 A K i' _51694 _51693 _51695).
Proof. exact (MK_COMB (@lem4473439 A K i' _51693 _51694 _51695) (@lem4473440 A K _51694 _51693 _51695)). Qed.
Lemma lem4473442 {A K : Type'} (i' : type843 A K) (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) : (term614 A K i' _51693 _51694 _51695) = (term640 A K i' _51694 _51693 _51695).
Proof. exact (TRANS (@lem4473434 A K i' _51694 _51693 _51695) (@lem4473441 A K i' _51694 _51693 _51695)). Qed.
Lemma lem4473445 {A K : Type'} (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term640 A K i' _51694 _51693 _51695.
Proof. exact (EQ_MP (@lem4473442 A K i' _51694 _51693 _51695) (@lem4473323 A K _51693 _51694 _51695 i' h1)). Qed.
Lemma lem4473446 {A K : Type'} (_51694 : type1470 A K) (_51693 : K -> Prop) (_51695 : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term640 A K i' _51694 _51693 _51695.
Proof. exact (@lem4473445 A K _51694 _51693 _51695 i' h1). Qed.
Lemma lem4473447 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (i' : type843 A K) (h1 : term310 A K i') : term640 A K i' t k s.
Proof. exact (@lem4473446 A K t k s i' h1). Qed.
Lemma lem4473450 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term537 A K t k s) (h2 : term310 A K i') (h3 : term103 A K t u k s) : term535 A K t k s.
Proof. exact (@lem4473447 A K t k s i' h2 (@lem4473431 A K i' t u k s h1 h2 h3)). Qed.
Lemma lem4473451 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i') (h2 : term103 A K t u k s) : term641 A K t k s.
Proof. exact (fun h0 : term537 A K t k s => @lem4473450 A K i' t u k s h0 h1 h2). Qed.
Lemma lem4473453 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4473454 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : (term641 A K t k s) = (term535 A K t k s).
Proof. exact (@lem4473453 (term535 A K t k s)). Qed.
Lemma lem4473455 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i') (h2 : term103 A K t u k s) : term535 A K t k s.
Proof. exact (EQ_MP (@lem4473454 A K t k s) (@lem4473451 A K i' t u k s h1 h2)). Qed.
Lemma lem4473458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4473460 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : (term537 A K t k s) = (term642 A K t k s).
Proof. exact (@lem4473458 (term535 A K t k s)). Qed.
Lemma lem4473463 {A K : Type'} (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term103 A K t u k s) : term642 A K t k s.
Proof. exact (EQ_MP (@lem4473460 A K t k s) (@lem4473225 A K t u k s h1)). Qed.
Lemma lem4473466 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i') (h2 : term103 A K t u k s) : False.
Proof. exact (@lem4473463 A K t u k s h2 (@lem4473455 A K i' t u k s h1 h2)). Qed.
Lemma lem4473467 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i') (h2 : term103 A K t u k s) : term643.
Proof. exact (fun h0 : ~ False => @lem4473466 A K i' t u k s h1 h2). Qed.
Lemma lem4473469 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4473470 : term643 = False.
Proof. exact (@lem4473469 False). Qed.
Lemma lem4473472 {A K : Type'} (i' : type843 A K) (t : type1470 A K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term310 A K i') (h2 : term103 A K t u k s) : False.
Proof. exact (EQ_MP (@lem4473470) (@lem4473467 A K i' t u k s h1 h2)). Qed.
Lemma lem4473473 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (i' : type843 A K) (h1 : term25 A K u k s) (h2 : term310 A K i') : False.
Proof. exact (ex_elim (@lem4470350 A K u k s h1) (fun t : type1470 A K => fun h0 : term105 A K u k s t => @lem4473472 A K i' t u k s h2 h0)). Qed.
Lemma lem4473474 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term26 A K) (h2 : term25 A K u k s) : False.
Proof. exact (ex_elim (@lem4471250 A K h1) (fun i' : type843 A K => fun h0 : term312 A K i' => @lem4473473 A K u k s i' h2 h0)). Qed.
Lemma lem4473475 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term26 A K) (h2 : term27 A K) (h3 : term25 A K u k s) : False.
Proof. exact (ex_elim (@lem4472150 A K h2) (fun i : type842 A K => fun h0 : term513 A K i => @lem4473474 A K u k s h1 h3)). Qed.
Lemma lem4473476 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term26 A K) (h2 : term25 A K u k s) : term32 A K.
Proof. exact (fun h0 : term27 A K => @lem4473475 A K u k s h1 h0 h2). Qed.
Lemma lem4473477 {A K : Type'} : (term32 A K) = (term33 A K).
Proof. exact (@lem69 (term27 A K)). Qed.
Lemma lem4473478 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term26 A K) (h2 : term25 A K u k s) : term33 A K.
Proof. exact (EQ_MP (@lem4473477 A K) (@lem4473476 A K u k s h1 h2)). Qed.
Lemma lem4473479 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term36 A K.
Proof. exact (fun h0 : term26 A K => @lem4473478 A K u k s h0 h1). Qed.
Lemma lem4473480 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term38 A K u k s.
Proof. exact (fun h0 : term25 A K u k s => @lem4473479 A K u k s h0). Qed.
Lemma lem4473485 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term42 A K k s.
Proof. exact (fun u : type1223 A K => @lem4473480 A K u k s). Qed.
Lemma lem4473490 {A K : Type'} (s : type1470 A K) : term46 A K s.
Proof. exact (fun k : K -> Prop => @lem4473485 A K k s). Qed.
Lemma lem4473495 {A K : Type'} : term50 A K.
Proof. exact (fun s : type1470 A K => @lem4473490 A K s). Qed.
Lemma lem4473496 {A K : Type'} : term49 A K.
Proof. exact (EQ_MP (@lem4470200 A K) (@lem4473495 A K)). Qed.
Lemma lem4473497 {A K : Type'} (s : type1470 A K) : term644 A K s.
Proof. exact (@lem4473496 A K s). Qed.
Lemma lem4473498 {A K : Type'} (s : type1470 A K) : (term644 A K s) = (term45 A K s).
Proof. exact (eq_refl (term644 A K s)). Qed.
Lemma lem4473499 {A K : Type'} (s : type1470 A K) : term45 A K s.
Proof. exact (EQ_MP (@lem4473498 A K s) (@lem4473497 A K s)). Qed.
Lemma lem4473500 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term645 A K s k.
Proof. exact (@lem4473499 A K s k). Qed.
Lemma lem4473501 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term645 A K s k) = (term41 A K k s).
Proof. exact (eq_refl (term645 A K s k)). Qed.
Lemma lem4473502 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term41 A K k s.
Proof. exact (EQ_MP (@lem4473501 A K k s) (@lem4473500 A K s k)). Qed.
Lemma lem4473503 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (u : type1223 A K) : term646 A K k s u.
Proof. exact (@lem4473502 A K k s u). Qed.
Lemma lem4473504 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term646 A K k s u) = (term28 A K u k s).
Proof. exact (eq_refl (term646 A K k s u)). Qed.
Lemma lem4473505 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term28 A K u k s.
Proof. exact (EQ_MP (@lem4473504 A K u k s) (@lem4473503 A K k s u)). Qed.
Lemma lem4473507 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term28 A K u k s.
Proof. exact (@lem4469878 A K u k s (@lem4473505 A K u k s)). Qed.
Lemma lem4473508 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term35 A K.
Proof. exact (@lem4473507 A K u k s (@lem4469857 A K u k s h1)). Qed.
Lemma lem4473509 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : term32 A K.
Proof. exact (@lem4473508 A K u k s h1 (@lem4469858 A K)). Qed.
Lemma lem4473510 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : False.
Proof. exact (@lem4473509 A K u k s h1 (@lem4469862 A K)). Qed.
Lemma lem4473511 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : (term25 A K u k s) = False.
Proof. exact (prop_ext (fun h2 : term25 A K u k s => @lem4473510 A K u k s h1) (fun h2 : False => @lem4469857 A K u k s h1)). Qed.
Lemma lem4473512 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term25 A K u k s) : False.
Proof. exact (EQ_MP (@lem4473511 A K u k s h1) (@lem4469857 A K u k s h1)). Qed.
Lemma lem4473513 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term24 A K u k s.
Proof. exact (fun h0 : term25 A K u k s => @lem4473512 A K u k s h0). Qed.
Lemma lem4473514 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term23 A K u k s.
Proof. exact (EQ_MP (@lem4469856 A K u k s) (@lem4473513 A K u k s)). Qed.
Lemma lem4473518 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4469840 A s t) (@lem4469839 A s t)). Qed.
Lemma lem4473519 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (@SUBSET (prod K A) s t) = (term647 A K s t).
Proof. exact (@lem4473518 (prod K A) s t). Qed.
Lemma lem4473520 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term21 A K u k s) = (term648 A K u k s).
Proof. exact (@lem4473519 A K u (@disjoint_union A K k s)). Qed.
Lemma lem4473527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473528 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term649 A K u k s) = (term650 A K u k s).
Proof. exact (MK_COMB (@lem4473527) (@lem4473520 A K u k s)). Qed.
Lemma lem4473534 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem4469834 A s t) (@lem4469833 A s t)). Qed.
Lemma lem4473535 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (s = t) = (term651 A K s t).
Proof. exact (@lem4473534 (prod K A) s t). Qed.
Lemma lem4473536 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (u = (term652 A K k u)) = (term653 A K k u).
Proof. exact (@lem4473535 A K u (term652 A K k u)). Qed.
Lemma lem4473549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4473550 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term654 A K k u) = (term655 A K k u).
Proof. exact (MK_COMB (@lem4473549) (@lem4473536 A K k u)). Qed.
Lemma lem4473558 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4469840 A s t) (@lem4469839 A s t)). Qed.
Lemma lem4473559 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term20 A s t).
Proof. exact (@lem4473558 A s t). Qed.
Lemma lem4473560 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term656 A K u s i) = (term657 A K u s i).
Proof. exact (@lem4473559 A (term658 A K u i) (s i)). Qed.
Lemma lem4473568 {A B : Type'} (f : A -> B) (y : A) : (term659 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4473569 {A K : Type'} (f : type1470 A K) (y : K) : (term660 A K f y) = (f y).
Proof. exact (@lem4473568 K (A -> Prop) f y). Qed.
Lemma lem4473570 {A K : Type'} (u : type1223 A K) (i : K) : (term661 A K u i) = (term658 A K u i).
Proof. exact (@lem4473569 A K (term662 A K u) i). Qed.
Lemma lem4473571 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (eq_refl (term658 A K u i)). Qed.
Lemma lem4473572 {A K : Type'} (u : type1223 A K) : (term664 A K u) = (term662 A K u).
Proof. exact (fun_ext (fun i : K => @lem4473571 A K i u)). Qed.
Lemma lem4473573 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4473574 {A K : Type'} (u : type1223 A K) (i : K) : (term661 A K u i) = (term658 A K u i).
Proof. exact (MK_COMB (@lem4473572 A K u) (@lem4473573 K i)). Qed.
Lemma lem4473575 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4473576 {A K : Type'} (u : type1223 A K) (i : K) : (term665 A K u i) = (term666 A K u i).
Proof. exact (MK_COMB (@lem4473575 A) (@lem4473574 A K u i)). Qed.
Lemma lem4473577 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (eq_refl (term658 A K u i)). Qed.
Lemma lem4473578 {A K : Type'} (i : K) (u : type1223 A K) : ((term661 A K u i) = (term658 A K u i)) = ((term658 A K u i) = (term663 A K i u)).
Proof. exact (MK_COMB (@lem4473576 A K u i) (@lem4473577 A K i u)). Qed.
Lemma lem4473579 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (EQ_MP (@lem4473578 A K i u) (@lem4473570 A K u i)). Qed.
Lemma lem4473584 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4473585 {A K : Type'} (x : A) (i : K) (u : type1223 A K) : (term667 A K x u i) = (term668 A K x i u).
Proof. exact (MK_COMB (@lem4473584 A x) (@lem4473579 A K i u)). Qed.
Lemma lem4473586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473587 {A K : Type'} (x : A) (i : K) (u : type1223 A K) : (term669 A K x u i) = (term670 A K x i u).
Proof. exact (MK_COMB (@lem4473586) (@lem4473585 A K x i u)). Qed.
Lemma lem4473588 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term671 A K x s i) = (term671 A K x s i).
Proof. exact (eq_refl (term671 A K x s i)). Qed.
Lemma lem4473589 {A K : Type'} (u : type1223 A K) (x : A) (s : type1470 A K) (i : K) : (term672 A K u x s i) = (term673 A K u x s i).
Proof. exact (MK_COMB (@lem4473587 A K x i u) (@lem4473588 A K x s i)). Qed.
Lemma lem4473592 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term674 A K u s i) = (term675 A K u s i).
Proof. exact (fun_ext (fun x : A => @lem4473589 A K u x s i)). Qed.
Lemma lem4473593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4473594 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term657 A K u s i) = (term676 A K u s i).
Proof. exact (MK_COMB (@lem4473593 A) (@lem4473592 A K u s i)). Qed.
Lemma lem4473599 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term656 A K u s i) = (term676 A K u s i).
Proof. exact (TRANS (@lem4473560 A K u s i) (@lem4473594 A K u s i)). Qed.
Lemma lem4473600 {K : Type'} (i : K) (k : K -> Prop) : (term677 K i k) = (term677 K i k).
Proof. exact (eq_refl (term677 K i k)). Qed.
Lemma lem4473601 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term678 A K k u s i) = (term679 A K k u s i).
Proof. exact (MK_COMB (@lem4473600 K i k) (@lem4473599 A K u s i)). Qed.
Lemma lem4473604 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term680 A K k u s) = (term681 A K k u s).
Proof. exact (fun_ext (fun i : K => @lem4473601 A K k u s i)). Qed.
Lemma lem4473605 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4473606 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term682 A K k u s) = (term683 A K k u s).
Proof. exact (MK_COMB (@lem4473605 K) (@lem4473604 A K k u s)). Qed.
Lemma lem4473611 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term684 A K k u s) = (term685 A K k u s).
Proof. exact (MK_COMB (@lem4473550 A K k u) (@lem4473606 A K k u s)). Qed.
Lemma lem4473614 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term686 A K k u s) = (term687 A K k u s).
Proof. exact (MK_COMB (@lem4473528 A K u k s) (@lem4473611 A K k u s)). Qed.
Lemma lem4473617 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term687 A K k u s) = (term686 A K k u s).
Proof. exact (SYM (@lem4473614 A K k u s)). Qed.
Lemma lem4473625 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term7 _5106 _5107 P) = (term8 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4469822 _5106 _5107 P) (@lem4469821 _5106 _5107 P)). Qed.
Lemma lem4473626 {A K : Type'} (P : type1223 A K) : (term7 A K P) = (term8 A K P).
Proof. exact (@lem4473625 A K P). Qed.
Lemma lem4473627 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term688 A K u k s) = (term689 A K u k s).
Proof. exact (@lem4473626 A K (term690 A K u k s)). Qed.
Lemma lem4473628 {A K : Type'} (u : type1223 A K) (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term691 A K u k s x) = (term692 A K u x k s).
Proof. exact (eq_refl (term691 A K u k s x)). Qed.
Lemma lem4473629 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term693 A K u k s) = (term690 A K u k s).
Proof. exact (fun_ext (fun x : prod K A => @lem4473628 A K u x k s)). Qed.
Lemma lem4473630 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4473631 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term688 A K u k s) = (term648 A K u k s).
Proof. exact (MK_COMB (@lem4473630 A K) (@lem4473629 A K u k s)). Qed.
Lemma lem4473632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473633 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term694 A K u k s) = (term695 A K u k s).
Proof. exact (MK_COMB (@lem4473632) (@lem4473631 A K u k s)). Qed.
Lemma lem4473634 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term696 A K u k s p1 p2) = (term697 A K u p1 p2 k s).
Proof. exact (eq_refl (term696 A K u k s p1 p2)). Qed.
Lemma lem4473635 {A K : Type'} (u : type1223 A K) (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term698 A K u k s p1) = (term699 A K u p1 k s).
Proof. exact (fun_ext (fun p2 : A => @lem4473634 A K u p1 p2 k s)). Qed.
Lemma lem4473636 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4473637 {A K : Type'} (u : type1223 A K) (p1 : K) (k : K -> Prop) (s : type1470 A K) : (term700 A K u k s p1) = (term701 A K u p1 k s).
Proof. exact (MK_COMB (@lem4473636 A) (@lem4473635 A K u p1 k s)). Qed.
Lemma lem4473638 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term702 A K u k s) = (term703 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4473637 A K u p1 k s)). Qed.
Lemma lem4473639 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4473640 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term689 A K u k s) = (term704 A K u k s).
Proof. exact (MK_COMB (@lem4473639 K) (@lem4473638 A K u k s)). Qed.
Lemma lem4473641 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : ((term688 A K u k s) = (term689 A K u k s)) = ((term648 A K u k s) = (term704 A K u k s)).
Proof. exact (MK_COMB (@lem4473633 A K u k s) (@lem4473640 A K u k s)). Qed.
Lemma lem4473642 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term648 A K u k s) = (term704 A K u k s).
Proof. exact (EQ_MP (@lem4473641 A K u k s) (@lem4473627 A K u k s)). Qed.
Lemma lem4473658 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (EQ_MP (@lem4469828 A K k s) (@lem4469827 A K k s)). Qed.
Lemma lem4473659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (@lem4473658 A K k s). Qed.
Lemma lem4473670 {A K : Type'} (p1 : K) (p2 : A) : (term705 A K p1 p2) = (term705 A K p1 p2).
Proof. exact (eq_refl (term705 A K p1 p2)). Qed.
Lemma lem4473671 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term706 A K p1 p2 k s) = (term707 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4473670 A K p1 p2) (@lem4473659 A K k s)). Qed.
Lemma lem4473673 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term5 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4469819 _88435 _88436 P a b) (@lem4469818 _88435 _88436 P a b)). Qed.
Lemma lem4473674 {A K : Type'} (P : type1470 A K) (a : K) (b : A) : (term5 A K a b P) = (P a b).
Proof. exact (@lem4473673 A K P a b). Qed.
Lemma lem4473675 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term708 A K p1 p2 k s) = (term709 A K k s p1 p2).
Proof. exact (@lem4473674 A K (term710 A K k s) p1 p2). Qed.
Lemma lem4473676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term711 A K k s i) = (term712 A K k s i).
Proof. exact (eq_refl (term711 A K k s i)). Qed.
Lemma lem4473677 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4473678 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term709 A K k s i x) = (term713 A K k s i x).
Proof. exact (MK_COMB (@lem4473676 A K k s i) (@lem4473677 A x)). Qed.
Lemma lem4473679 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term713 A K k s i x) = (term714 A K k x s i).
Proof. exact (eq_refl (term713 A K k s i x)). Qed.
Lemma lem4473680 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term709 A K k s i x) = (term714 A K k x s i).
Proof. exact (TRANS (@lem4473678 A K k s i x) (@lem4473679 A K k x s i)). Qed.
Lemma lem4473681 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4473682 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term715 A K GEN_PVAR_143 k s i x) = (term716 A K GEN_PVAR_143 k x s i).
Proof. exact (MK_COMB (@lem4473681 A K GEN_PVAR_143) (@lem4473680 A K k x s i)). Qed.
Lemma lem4473683 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4473684 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term717 A K GEN_PVAR_143 k s i x) = (term718 A K GEN_PVAR_143 k s i x).
Proof. exact (MK_COMB (@lem4473682 A K GEN_PVAR_143 k x s i) (@lem4473683 A K i x)). Qed.
Lemma lem4473685 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term719 A K GEN_PVAR_143 k s i) = (term720 A K GEN_PVAR_143 k s i).
Proof. exact (fun_ext (fun x : A => @lem4473684 A K GEN_PVAR_143 k s i x)). Qed.
Lemma lem4473686 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4473687 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term721 A K GEN_PVAR_143 k s i) = (term722 A K GEN_PVAR_143 k s i).
Proof. exact (MK_COMB (@lem4473686 A) (@lem4473685 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4473688 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term723 A K GEN_PVAR_143 k s) = (term724 A K GEN_PVAR_143 k s).
Proof. exact (fun_ext (fun i : K => @lem4473687 A K GEN_PVAR_143 k s i)). Qed.
Lemma lem4473689 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4473690 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term725 A K GEN_PVAR_143 k s) = (term726 A K GEN_PVAR_143 k s).
Proof. exact (MK_COMB (@lem4473689 K) (@lem4473688 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4473691 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term727 A K k s) = (term728 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4473690 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4473692 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4473693 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term729 A K k s) = (term12 A K k s).
Proof. exact (MK_COMB (@lem4473692 A K) (@lem4473691 A K k s)). Qed.
Lemma lem4473694 {A K : Type'} (p1 : K) (p2 : A) : (term705 A K p1 p2) = (term705 A K p1 p2).
Proof. exact (eq_refl (term705 A K p1 p2)). Qed.
Lemma lem4473695 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term708 A K p1 p2 k s) = (term707 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4473694 A K p1 p2) (@lem4473693 A K k s)). Qed.
Lemma lem4473696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473697 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (s : type1470 A K) : (term730 A K p1 p2 k s) = (term731 A K p1 p2 k s).
Proof. exact (MK_COMB (@lem4473696) (@lem4473695 A K p1 p2 k s)). Qed.
Lemma lem4473698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term711 A K k s p1) = (term712 A K k s p1).
Proof. exact (eq_refl (term711 A K k s p1)). Qed.
Lemma lem4473699 {A : Type'} (p2 : A) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem4473700 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term709 A K k s p1 p2) = (term713 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4473698 A K k s p1) (@lem4473699 A p2)). Qed.
Lemma lem4473701 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term713 A K k s p1 p2) = (term714 A K k p2 s p1).
Proof. exact (eq_refl (term713 A K k s p1 p2)). Qed.
Lemma lem4473702 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term709 A K k s p1 p2) = (term714 A K k p2 s p1).
Proof. exact (TRANS (@lem4473700 A K k s p1 p2) (@lem4473701 A K k p2 s p1)). Qed.
Lemma lem4473703 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : ((term708 A K p1 p2 k s) = (term709 A K k s p1 p2)) = ((term707 A K p1 p2 k s) = (term714 A K k p2 s p1)).
Proof. exact (MK_COMB (@lem4473697 A K p1 p2 k s) (@lem4473702 A K k p2 s p1)). Qed.
Lemma lem4473704 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term707 A K p1 p2 k s) = (term714 A K k p2 s p1).
Proof. exact (EQ_MP (@lem4473703 A K k p2 s p1) (@lem4473675 A K k s p1 p2)). Qed.
Lemma lem4473707 {A K : Type'} (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term706 A K p1 p2 k s) = (term714 A K k p2 s p1).
Proof. exact (TRANS (@lem4473671 A K p1 p2 k s) (@lem4473704 A K k p2 s p1)). Qed.
Lemma lem4473708 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) : (term732 A K p1 p2 u) = (term732 A K p1 p2 u).
Proof. exact (eq_refl (term732 A K p1 p2 u)). Qed.
Lemma lem4473709 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (p2 : A) (s : type1470 A K) (p1 : K) : (term697 A K u p1 p2 k s) = (term733 A K u k p2 s p1).
Proof. exact (MK_COMB (@lem4473708 A K p1 p2 u) (@lem4473707 A K k p2 s p1)). Qed.
Lemma lem4473712 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term699 A K u p1 k s) = (term734 A K u k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4473709 A K u k p2 s p1)). Qed.
Lemma lem4473713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4473714 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term701 A K u p1 k s) = (term735 A K u k s p1).
Proof. exact (MK_COMB (@lem4473713 A) (@lem4473712 A K u k s p1)). Qed.
Lemma lem4473721 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term703 A K u k s) = (term736 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4473714 A K u k s p1)). Qed.
Lemma lem4473722 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4473723 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term704 A K u k s) = (term737 A K u k s).
Proof. exact (MK_COMB (@lem4473722 K) (@lem4473721 A K u k s)). Qed.
Lemma lem4473730 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term648 A K u k s) = (term737 A K u k s).
Proof. exact (TRANS (@lem4473642 A K u k s) (@lem4473723 A K u k s)). Qed.
Lemma lem4473731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473732 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term650 A K u k s) = (term738 A K u k s).
Proof. exact (MK_COMB (@lem4473731) (@lem4473730 A K u k s)). Qed.
Lemma lem4473740 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term7 _5106 _5107 P) = (term8 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4469822 _5106 _5107 P) (@lem4469821 _5106 _5107 P)). Qed.
Lemma lem4473741 {A K : Type'} (P : type1223 A K) : (term7 A K P) = (term8 A K P).
Proof. exact (@lem4473740 A K P). Qed.
Lemma lem4473742 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term739 A K k u) = (term740 A K k u).
Proof. exact (@lem4473741 A K (term741 A K k u)). Qed.
Lemma lem4473743 {A K : Type'} (x : prod K A) (k : K -> Prop) (u : type1223 A K) : (term742 A K k u x) = ((@IN (prod K A) x u) = (term743 A K x k u)).
Proof. exact (eq_refl (term742 A K k u x)). Qed.
Lemma lem4473744 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term744 A K k u) = (term741 A K k u).
Proof. exact (fun_ext (fun x : prod K A => @lem4473743 A K x k u)). Qed.
Lemma lem4473745 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4473746 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term739 A K k u) = (term653 A K k u).
Proof. exact (MK_COMB (@lem4473745 A K) (@lem4473744 A K k u)). Qed.
Lemma lem4473747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473748 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term745 A K k u) = (term746 A K k u).
Proof. exact (MK_COMB (@lem4473747) (@lem4473746 A K k u)). Qed.
Lemma lem4473749 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (u : type1223 A K) : (term747 A K k u p1 p2) = ((term748 A K p1 p2 u) = (term749 A K p1 p2 k u)).
Proof. exact (eq_refl (term747 A K k u p1 p2)). Qed.
Lemma lem4473750 {A K : Type'} (p1 : K) (k : K -> Prop) (u : type1223 A K) : (term750 A K k u p1) = (term751 A K p1 k u).
Proof. exact (fun_ext (fun p2 : A => @lem4473749 A K p1 p2 k u)). Qed.
Lemma lem4473751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4473752 {A K : Type'} (p1 : K) (k : K -> Prop) (u : type1223 A K) : (term752 A K k u p1) = (term753 A K p1 k u).
Proof. exact (MK_COMB (@lem4473751 A) (@lem4473750 A K p1 k u)). Qed.
Lemma lem4473753 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term754 A K k u) = (term755 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4473752 A K p1 k u)). Qed.
Lemma lem4473754 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4473755 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term740 A K k u) = (term756 A K k u).
Proof. exact (MK_COMB (@lem4473754 K) (@lem4473753 A K k u)). Qed.
Lemma lem4473756 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : ((term739 A K k u) = (term740 A K k u)) = ((term653 A K k u) = (term756 A K k u)).
Proof. exact (MK_COMB (@lem4473748 A K k u) (@lem4473755 A K k u)). Qed.
Lemma lem4473757 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term653 A K k u) = (term756 A K k u).
Proof. exact (EQ_MP (@lem4473756 A K k u) (@lem4473742 A K k u)). Qed.
Lemma lem4473773 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (EQ_MP (@lem4469828 A K k s) (@lem4469827 A K k s)). Qed.
Lemma lem4473774 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term12 A K k s).
Proof. exact (@lem4473773 A K k s). Qed.
Lemma lem4473775 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term652 A K k u) = (term757 A K k u).
Proof. exact (@lem4473774 A K k (term662 A K u)). Qed.
Lemma lem4473787 {A B : Type'} (f : A -> B) (y : A) : (term659 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4473788 {A K : Type'} (f : type1470 A K) (y : K) : (term660 A K f y) = (f y).
Proof. exact (@lem4473787 K (A -> Prop) f y). Qed.
Lemma lem4473789 {A K : Type'} (u : type1223 A K) (i : K) : (term661 A K u i) = (term658 A K u i).
Proof. exact (@lem4473788 A K (term662 A K u) i). Qed.
Lemma lem4473790 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (eq_refl (term658 A K u i)). Qed.
Lemma lem4473791 {A K : Type'} (u : type1223 A K) : (term664 A K u) = (term662 A K u).
Proof. exact (fun_ext (fun i : K => @lem4473790 A K i u)). Qed.
Lemma lem4473792 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4473793 {A K : Type'} (u : type1223 A K) (i : K) : (term661 A K u i) = (term658 A K u i).
Proof. exact (MK_COMB (@lem4473791 A K u) (@lem4473792 K i)). Qed.
Lemma lem4473794 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4473795 {A K : Type'} (u : type1223 A K) (i : K) : (term665 A K u i) = (term666 A K u i).
Proof. exact (MK_COMB (@lem4473794 A) (@lem4473793 A K u i)). Qed.
Lemma lem4473796 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (eq_refl (term658 A K u i)). Qed.
Lemma lem4473797 {A K : Type'} (i : K) (u : type1223 A K) : ((term661 A K u i) = (term658 A K u i)) = ((term658 A K u i) = (term663 A K i u)).
Proof. exact (MK_COMB (@lem4473795 A K u i) (@lem4473796 A K i u)). Qed.
Lemma lem4473798 {A K : Type'} (i : K) (u : type1223 A K) : (term658 A K u i) = (term663 A K i u).
Proof. exact (EQ_MP (@lem4473797 A K i u) (@lem4473789 A K u i)). Qed.
Lemma lem4473803 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4473804 {A K : Type'} (x : A) (i : K) (u : type1223 A K) : (term667 A K x u i) = (term668 A K x i u).
Proof. exact (MK_COMB (@lem4473803 A x) (@lem4473798 A K i u)). Qed.
Lemma lem4473805 {K : Type'} (i : K) (k : K -> Prop) : (term758 K i k) = (term758 K i k).
Proof. exact (eq_refl (term758 K i k)). Qed.
Lemma lem4473806 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (u : type1223 A K) : (term759 A K k x u i) = (term760 A K k x i u).
Proof. exact (MK_COMB (@lem4473805 K i k) (@lem4473804 A K x i u)). Qed.
Lemma lem4473809 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4473810 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (i : K) (u : type1223 A K) : (term761 A K GEN_PVAR_143 k x u i) = (term762 A K GEN_PVAR_143 k x i u).
Proof. exact (MK_COMB (@lem4473809 A K GEN_PVAR_143) (@lem4473806 A K k x i u)). Qed.
Lemma lem4473811 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4473812 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) (x : A) : (term763 A K GEN_PVAR_143 k u i x) = (term764 A K GEN_PVAR_143 k u i x).
Proof. exact (MK_COMB (@lem4473810 A K GEN_PVAR_143 k x i u) (@lem4473811 A K i x)). Qed.
Lemma lem4473813 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) : (term765 A K GEN_PVAR_143 k u i) = (term766 A K GEN_PVAR_143 k u i).
Proof. exact (fun_ext (fun x : A => @lem4473812 A K GEN_PVAR_143 k u i x)). Qed.
Lemma lem4473814 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4473815 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) : (term767 A K GEN_PVAR_143 k u i) = (term768 A K GEN_PVAR_143 k u i).
Proof. exact (MK_COMB (@lem4473814 A) (@lem4473813 A K GEN_PVAR_143 k u i)). Qed.
Lemma lem4473820 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) : (term769 A K GEN_PVAR_143 k u) = (term770 A K GEN_PVAR_143 k u).
Proof. exact (fun_ext (fun i : K => @lem4473815 A K GEN_PVAR_143 k u i)). Qed.
Lemma lem4473821 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4473822 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) : (term771 A K GEN_PVAR_143 k u) = (term772 A K GEN_PVAR_143 k u).
Proof. exact (MK_COMB (@lem4473821 K) (@lem4473820 A K GEN_PVAR_143 k u)). Qed.
Lemma lem4473827 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term773 A K k u) = (term774 A K k u).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4473822 A K GEN_PVAR_143 k u)). Qed.
Lemma lem4473828 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4473829 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term757 A K k u) = (term775 A K k u).
Proof. exact (MK_COMB (@lem4473828 A K) (@lem4473827 A K k u)). Qed.
Lemma lem4473830 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term652 A K k u) = (term775 A K k u).
Proof. exact (TRANS (@lem4473775 A K k u) (@lem4473829 A K k u)). Qed.
Lemma lem4473831 {A K : Type'} (p1 : K) (p2 : A) : (term705 A K p1 p2) = (term705 A K p1 p2).
Proof. exact (eq_refl (term705 A K p1 p2)). Qed.
Lemma lem4473832 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (u : type1223 A K) : (term749 A K p1 p2 k u) = (term776 A K p1 p2 k u).
Proof. exact (MK_COMB (@lem4473831 A K p1 p2) (@lem4473830 A K k u)). Qed.
Lemma lem4473834 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term5 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4469819 _88435 _88436 P a b) (@lem4469818 _88435 _88436 P a b)). Qed.
Lemma lem4473835 {A K : Type'} (P : type1470 A K) (a : K) (b : A) : (term5 A K a b P) = (P a b).
Proof. exact (@lem4473834 A K P a b). Qed.
Lemma lem4473836 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term777 A K p1 p2 k u) = (term778 A K k u p1 p2).
Proof. exact (@lem4473835 A K (term779 A K k u) p1 p2). Qed.
Lemma lem4473837 {A K : Type'} (k : K -> Prop) (i : K) (u : type1223 A K) : (term780 A K k u i) = (term781 A K k i u).
Proof. exact (eq_refl (term780 A K k u i)). Qed.
Lemma lem4473838 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4473839 {A K : Type'} (k : K -> Prop) (i : K) (u : type1223 A K) (x : A) : (term778 A K k u i x) = (term782 A K k i u x).
Proof. exact (MK_COMB (@lem4473837 A K k i u) (@lem4473838 A x)). Qed.
Lemma lem4473840 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (u : type1223 A K) : (term782 A K k i u x) = (term760 A K k x i u).
Proof. exact (eq_refl (term782 A K k i u x)). Qed.
Lemma lem4473841 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (u : type1223 A K) : (term778 A K k u i x) = (term760 A K k x i u).
Proof. exact (TRANS (@lem4473839 A K k i u x) (@lem4473840 A K k x i u)). Qed.
Lemma lem4473842 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4473843 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (x : A) (i : K) (u : type1223 A K) : (term783 A K GEN_PVAR_143 k u i x) = (term762 A K GEN_PVAR_143 k x i u).
Proof. exact (MK_COMB (@lem4473842 A K GEN_PVAR_143) (@lem4473841 A K k x i u)). Qed.
Lemma lem4473844 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4473845 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) (x : A) : (term784 A K GEN_PVAR_143 k u i x) = (term764 A K GEN_PVAR_143 k u i x).
Proof. exact (MK_COMB (@lem4473843 A K GEN_PVAR_143 k x i u) (@lem4473844 A K i x)). Qed.
Lemma lem4473846 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) : (term785 A K GEN_PVAR_143 k u i) = (term766 A K GEN_PVAR_143 k u i).
Proof. exact (fun_ext (fun x : A => @lem4473845 A K GEN_PVAR_143 k u i x)). Qed.
Lemma lem4473847 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4473848 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) (i : K) : (term786 A K GEN_PVAR_143 k u i) = (term768 A K GEN_PVAR_143 k u i).
Proof. exact (MK_COMB (@lem4473847 A) (@lem4473846 A K GEN_PVAR_143 k u i)). Qed.
Lemma lem4473849 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) : (term787 A K GEN_PVAR_143 k u) = (term770 A K GEN_PVAR_143 k u).
Proof. exact (fun_ext (fun i : K => @lem4473848 A K GEN_PVAR_143 k u i)). Qed.
Lemma lem4473850 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4473851 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (u : type1223 A K) : (term788 A K GEN_PVAR_143 k u) = (term772 A K GEN_PVAR_143 k u).
Proof. exact (MK_COMB (@lem4473850 K) (@lem4473849 A K GEN_PVAR_143 k u)). Qed.
Lemma lem4473852 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term789 A K k u) = (term774 A K k u).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4473851 A K GEN_PVAR_143 k u)). Qed.
Lemma lem4473853 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4473854 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term790 A K k u) = (term775 A K k u).
Proof. exact (MK_COMB (@lem4473853 A K) (@lem4473852 A K k u)). Qed.
Lemma lem4473855 {A K : Type'} (p1 : K) (p2 : A) : (term705 A K p1 p2) = (term705 A K p1 p2).
Proof. exact (eq_refl (term705 A K p1 p2)). Qed.
Lemma lem4473856 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (u : type1223 A K) : (term777 A K p1 p2 k u) = (term776 A K p1 p2 k u).
Proof. exact (MK_COMB (@lem4473855 A K p1 p2) (@lem4473854 A K k u)). Qed.
Lemma lem4473857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4473858 {A K : Type'} (p1 : K) (p2 : A) (k : K -> Prop) (u : type1223 A K) : (term791 A K p1 p2 k u) = (term792 A K p1 p2 k u).
Proof. exact (MK_COMB (@lem4473857) (@lem4473856 A K p1 p2 k u)). Qed.
Lemma lem4473859 {A K : Type'} (k : K -> Prop) (p1 : K) (u : type1223 A K) : (term780 A K k u p1) = (term781 A K k p1 u).
Proof. exact (eq_refl (term780 A K k u p1)). Qed.
Lemma lem4473860 {A : Type'} (p2 : A) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem4473861 {A K : Type'} (k : K -> Prop) (p1 : K) (u : type1223 A K) (p2 : A) : (term778 A K k u p1 p2) = (term782 A K k p1 u p2).
Proof. exact (MK_COMB (@lem4473859 A K k p1 u) (@lem4473860 A p2)). Qed.
Lemma lem4473862 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : (term782 A K k p1 u p2) = (term760 A K k p2 p1 u).
Proof. exact (eq_refl (term782 A K k p1 u p2)). Qed.
Lemma lem4473863 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : (term778 A K k u p1 p2) = (term760 A K k p2 p1 u).
Proof. exact (TRANS (@lem4473861 A K k p1 u p2) (@lem4473862 A K k p2 p1 u)). Qed.
Lemma lem4473864 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : ((term777 A K p1 p2 k u) = (term778 A K k u p1 p2)) = ((term776 A K p1 p2 k u) = (term760 A K k p2 p1 u)).
Proof. exact (MK_COMB (@lem4473858 A K p1 p2 k u) (@lem4473863 A K k p2 p1 u)). Qed.
Lemma lem4473865 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : (term776 A K p1 p2 k u) = (term760 A K k p2 p1 u).
Proof. exact (EQ_MP (@lem4473864 A K k p2 p1 u) (@lem4473836 A K k u p1 p2)). Qed.
Lemma lem4473872 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : (term749 A K p1 p2 k u) = (term760 A K k p2 p1 u).
Proof. exact (TRANS (@lem4473832 A K p1 p2 k u) (@lem4473865 A K k p2 p1 u)). Qed.
Lemma lem4473873 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) : (term793 A K p1 p2 u) = (term793 A K p1 p2 u).
Proof. exact (eq_refl (term793 A K p1 p2 u)). Qed.
Lemma lem4473874 {A K : Type'} (k : K -> Prop) (p2 : A) (p1 : K) (u : type1223 A K) : ((term748 A K p1 p2 u) = (term749 A K p1 p2 k u)) = ((term748 A K p1 p2 u) = (term760 A K k p2 p1 u)).
Proof. exact (MK_COMB (@lem4473873 A K p1 p2 u) (@lem4473872 A K k p2 p1 u)). Qed.
Lemma lem4473877 {A K : Type'} (k : K -> Prop) (p1 : K) (u : type1223 A K) : (term751 A K p1 k u) = (term794 A K k p1 u).
Proof. exact (fun_ext (fun p2 : A => @lem4473874 A K k p2 p1 u)). Qed.
Lemma lem4473878 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4473879 {A K : Type'} (k : K -> Prop) (p1 : K) (u : type1223 A K) : (term753 A K p1 k u) = (term795 A K k p1 u).
Proof. exact (MK_COMB (@lem4473878 A) (@lem4473877 A K k p1 u)). Qed.
Lemma lem4473886 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term755 A K k u) = (term796 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4473879 A K k p1 u)). Qed.
Lemma lem4473887 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4473888 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term756 A K k u) = (term797 A K k u).
Proof. exact (MK_COMB (@lem4473887 K) (@lem4473886 A K k u)). Qed.
Lemma lem4473895 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term653 A K k u) = (term797 A K k u).
Proof. exact (TRANS (@lem4473757 A K k u) (@lem4473888 A K k u)). Qed.
Lemma lem4473896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4473897 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term655 A K k u) = (term798 A K k u).
Proof. exact (MK_COMB (@lem4473896) (@lem4473895 A K k u)). Qed.
Lemma lem4473918 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term683 A K k u s) = (term683 A K k u s).
Proof. exact (eq_refl (term683 A K k u s)). Qed.
Lemma lem4473919 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term685 A K k u s) = (term799 A K k u s).
Proof. exact (MK_COMB (@lem4473897 A K k u) (@lem4473918 A K k u s)). Qed.
Lemma lem4473922 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term687 A K k u s) = (term800 A K k u s).
Proof. exact (MK_COMB (@lem4473732 A K u k s) (@lem4473919 A K k u s)). Qed.
Lemma lem4473925 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term800 A K k u s) = (term687 A K k u s).
Proof. exact (SYM (@lem4473922 A K k u s)). Qed.
Lemma lem4473991 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4473992 {A K : Type'} (P : type1223 A K) (x : prod K A) : (@IN (prod K A) x P) = (P x).
Proof. exact (@lem4473991 (prod K A) P x). Qed.
Lemma lem4473993 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term748 A K p1 p2 u) = (term801 A K u p1 p2).
Proof. exact (@lem4473992 A K u (@pair K A p1 p2)). Qed.
Lemma lem4473994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4473995 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term732 A K p1 p2 u) = (term802 A K u p1 p2).
Proof. exact (MK_COMB (@lem4473994) (@lem4473993 A K u p1 p2)). Qed.
Lemma lem4473999 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474000 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4473999 K P x). Qed.
Lemma lem4474001 {K : Type'} (k : K -> Prop) (p1 : K) : (@IN K p1 k) = (k p1).
Proof. exact (@lem4474000 K k p1). Qed.
Lemma lem4474002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4474003 {K : Type'} (k : K -> Prop) (p1 : K) : (term758 K p1 k) = (term803 K k p1).
Proof. exact (MK_COMB (@lem4474002) (@lem4474001 K k p1)). Qed.
Lemma lem4474005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474006 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4474005 A P x). Qed.
Lemma lem4474007 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term671 A K p2 s p1) = (s p1 p2).
Proof. exact (@lem4474006 A (s p1) p2). Qed.
Lemma lem4474008 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term714 A K k p2 s p1) = (term804 A K k s p1 p2).
Proof. exact (MK_COMB (@lem4474003 K k p1) (@lem4474007 A K s p1 p2)). Qed.
Lemma lem4474011 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term733 A K u k p2 s p1) = (term805 A K u k s p1 p2).
Proof. exact (MK_COMB (@lem4473995 A K u p1 p2) (@lem4474008 A K k s p1 p2)). Qed.
Lemma lem4474014 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term734 A K u k s p1) = (term806 A K u k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474011 A K u k s p1 p2)). Qed.
Lemma lem4474015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474016 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term735 A K u k s p1) = (term807 A K u k s p1).
Proof. exact (MK_COMB (@lem4474015 A) (@lem4474014 A K u k s p1)). Qed.
Lemma lem4474021 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term736 A K u k s) = (term808 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4474016 A K u k s p1)). Qed.
Lemma lem4474022 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474023 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term737 A K u k s) = (term809 A K u k s).
Proof. exact (MK_COMB (@lem4474022 K) (@lem4474021 A K u k s)). Qed.
Lemma lem4474028 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4474029 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term738 A K u k s) = (term810 A K u k s).
Proof. exact (MK_COMB (@lem4474028) (@lem4474023 A K u k s)). Qed.
Lemma lem4474043 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474044 {A K : Type'} (P : type1223 A K) (x : prod K A) : (@IN (prod K A) x P) = (P x).
Proof. exact (@lem4474043 (prod K A) P x). Qed.
Lemma lem4474045 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term748 A K p1 p2 u) = (term801 A K u p1 p2).
Proof. exact (@lem4474044 A K u (@pair K A p1 p2)). Qed.
Lemma lem4474046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474047 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term793 A K p1 p2 u) = (term811 A K u p1 p2).
Proof. exact (MK_COMB (@lem4474046) (@lem4474045 A K u p1 p2)). Qed.
Lemma lem4474051 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474052 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4474051 K P x). Qed.
Lemma lem4474053 {K : Type'} (k : K -> Prop) (p1 : K) : (@IN K p1 k) = (k p1).
Proof. exact (@lem4474052 K k p1). Qed.
Lemma lem4474054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4474055 {K : Type'} (k : K -> Prop) (p1 : K) : (term758 K p1 k) = (term803 K k p1).
Proof. exact (MK_COMB (@lem4474054) (@lem4474053 K k p1)). Qed.
Lemma lem4474057 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term812 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4474058 {A : Type'} (p : A -> Prop) (x : A) : (term812 A x p) = (p x).
Proof. exact (@lem4474057 A p x). Qed.
Lemma lem4474059 {A K : Type'} (p1 : K) (u : type1223 A K) (p2 : A) : (term813 A K p2 p1 u) = (term814 A K p1 u p2).
Proof. exact (@lem4474058 A (term815 A K p1 u) p2). Qed.
Lemma lem4474060 {A K : Type'} (p1 : K) (x : A) (u : type1223 A K) : (term814 A K p1 u x) = (term748 A K p1 x u).
Proof. exact (eq_refl (term814 A K p1 u x)). Qed.
Lemma lem4474061 {A : Type'} (GEN_PVAR_144 : A) : (@SETSPEC A GEN_PVAR_144) = (@SETSPEC A GEN_PVAR_144).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_144)). Qed.
Lemma lem4474062 {A K : Type'} (GEN_PVAR_144 : A) (p1 : K) (x : A) (u : type1223 A K) : (term816 A K GEN_PVAR_144 p1 u x) = (term817 A K GEN_PVAR_144 p1 x u).
Proof. exact (MK_COMB (@lem4474061 A GEN_PVAR_144) (@lem4474060 A K p1 x u)). Qed.
Lemma lem4474063 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4474064 {A K : Type'} (GEN_PVAR_144 : A) (p1 : K) (u : type1223 A K) (x : A) : (term818 A K GEN_PVAR_144 p1 u x) = (term819 A K GEN_PVAR_144 p1 u x).
Proof. exact (MK_COMB (@lem4474062 A K GEN_PVAR_144 p1 x u) (@lem4474063 A x)). Qed.
Lemma lem4474065 {A K : Type'} (GEN_PVAR_144 : A) (p1 : K) (u : type1223 A K) : (term820 A K GEN_PVAR_144 p1 u) = (term821 A K GEN_PVAR_144 p1 u).
Proof. exact (fun_ext (fun x : A => @lem4474064 A K GEN_PVAR_144 p1 u x)). Qed.
Lemma lem4474066 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474067 {A K : Type'} (GEN_PVAR_144 : A) (p1 : K) (u : type1223 A K) : (term822 A K GEN_PVAR_144 p1 u) = (term823 A K GEN_PVAR_144 p1 u).
Proof. exact (MK_COMB (@lem4474066 A) (@lem4474065 A K GEN_PVAR_144 p1 u)). Qed.
Lemma lem4474068 {A K : Type'} (p1 : K) (u : type1223 A K) : (term824 A K p1 u) = (term825 A K p1 u).
Proof. exact (fun_ext (fun GEN_PVAR_144 : A => @lem4474067 A K GEN_PVAR_144 p1 u)). Qed.
Lemma lem4474069 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4474070 {A K : Type'} (p1 : K) (u : type1223 A K) : (term826 A K p1 u) = (term663 A K p1 u).
Proof. exact (MK_COMB (@lem4474069 A) (@lem4474068 A K p1 u)). Qed.
Lemma lem4474071 {A : Type'} (p2 : A) : (@IN A p2) = (@IN A p2).
Proof. exact (eq_refl (@IN A p2)). Qed.
Lemma lem4474072 {A K : Type'} (p2 : A) (p1 : K) (u : type1223 A K) : (term813 A K p2 p1 u) = (term668 A K p2 p1 u).
Proof. exact (MK_COMB (@lem4474071 A p2) (@lem4474070 A K p1 u)). Qed.
Lemma lem4474073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474074 {A K : Type'} (p2 : A) (p1 : K) (u : type1223 A K) : (term827 A K p2 p1 u) = (term828 A K p2 p1 u).
Proof. exact (MK_COMB (@lem4474073) (@lem4474072 A K p2 p1 u)). Qed.
Lemma lem4474075 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) : (term814 A K p1 u p2) = (term748 A K p1 p2 u).
Proof. exact (eq_refl (term814 A K p1 u p2)). Qed.
Lemma lem4474076 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) : ((term813 A K p2 p1 u) = (term814 A K p1 u p2)) = ((term668 A K p2 p1 u) = (term748 A K p1 p2 u)).
Proof. exact (MK_COMB (@lem4474074 A K p2 p1 u) (@lem4474075 A K p1 p2 u)). Qed.
Lemma lem4474077 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) : (term668 A K p2 p1 u) = (term748 A K p1 p2 u).
Proof. exact (EQ_MP (@lem4474076 A K p1 p2 u) (@lem4474059 A K p1 u p2)). Qed.
Lemma lem4474079 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474080 {A K : Type'} (P : type1223 A K) (x : prod K A) : (@IN (prod K A) x P) = (P x).
Proof. exact (@lem4474079 (prod K A) P x). Qed.
Lemma lem4474081 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term748 A K p1 p2 u) = (term801 A K u p1 p2).
Proof. exact (@lem4474080 A K u (@pair K A p1 p2)). Qed.
Lemma lem4474082 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term668 A K p2 p1 u) = (term801 A K u p1 p2).
Proof. exact (TRANS (@lem4474077 A K p1 p2 u) (@lem4474081 A K u p1 p2)). Qed.
Lemma lem4474083 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term760 A K k p2 p1 u) = (term829 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474055 K k p1) (@lem4474082 A K u p1 p2)). Qed.
Lemma lem4474086 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : ((term748 A K p1 p2 u) = (term760 A K k p2 p1 u)) = ((term801 A K u p1 p2) = (term829 A K k u p1 p2)).
Proof. exact (MK_COMB (@lem4474047 A K u p1 p2) (@lem4474083 A K k u p1 p2)). Qed.
Lemma lem4474089 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term794 A K k p1 u) = (term830 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474086 A K k u p1 p2)). Qed.
Lemma lem4474090 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474091 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term795 A K k p1 u) = (term831 A K k u p1).
Proof. exact (MK_COMB (@lem4474090 A) (@lem4474089 A K k u p1)). Qed.
Lemma lem4474096 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term796 A K k u) = (term832 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474091 A K k u p1)). Qed.
Lemma lem4474097 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474098 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term797 A K k u) = (term833 A K k u).
Proof. exact (MK_COMB (@lem4474097 K) (@lem4474096 A K k u)). Qed.
Lemma lem4474103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4474104 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term798 A K k u) = (term834 A K k u).
Proof. exact (MK_COMB (@lem4474103) (@lem4474098 A K k u)). Qed.
Lemma lem4474112 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474113 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4474112 K P x). Qed.
Lemma lem4474114 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4474113 K k i). Qed.
Lemma lem4474115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4474116 {K : Type'} (k : K -> Prop) (i : K) : (term677 K i k) = (term835 K k i).
Proof. exact (MK_COMB (@lem4474115) (@lem4474114 K k i)). Qed.
Lemma lem4474124 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term812 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4474125 {A : Type'} (p : A -> Prop) (x : A) : (term812 A x p) = (p x).
Proof. exact (@lem4474124 A p x). Qed.
Lemma lem4474126 {A K : Type'} (i : K) (u : type1223 A K) (x : A) : (term813 A K x i u) = (term814 A K i u x).
Proof. exact (@lem4474125 A (term815 A K i u) x). Qed.
Lemma lem4474127 {A K : Type'} (i : K) (x : A) (u : type1223 A K) : (term814 A K i u x) = (term748 A K i x u).
Proof. exact (eq_refl (term814 A K i u x)). Qed.
Lemma lem4474128 {A : Type'} (GEN_PVAR_144 : A) : (@SETSPEC A GEN_PVAR_144) = (@SETSPEC A GEN_PVAR_144).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_144)). Qed.
Lemma lem4474129 {A K : Type'} (GEN_PVAR_144 : A) (i : K) (x : A) (u : type1223 A K) : (term816 A K GEN_PVAR_144 i u x) = (term817 A K GEN_PVAR_144 i x u).
Proof. exact (MK_COMB (@lem4474128 A GEN_PVAR_144) (@lem4474127 A K i x u)). Qed.
Lemma lem4474130 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4474131 {A K : Type'} (GEN_PVAR_144 : A) (i : K) (u : type1223 A K) (x : A) : (term818 A K GEN_PVAR_144 i u x) = (term819 A K GEN_PVAR_144 i u x).
Proof. exact (MK_COMB (@lem4474129 A K GEN_PVAR_144 i x u) (@lem4474130 A x)). Qed.
Lemma lem4474132 {A K : Type'} (GEN_PVAR_144 : A) (i : K) (u : type1223 A K) : (term820 A K GEN_PVAR_144 i u) = (term821 A K GEN_PVAR_144 i u).
Proof. exact (fun_ext (fun x : A => @lem4474131 A K GEN_PVAR_144 i u x)). Qed.
Lemma lem4474133 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474134 {A K : Type'} (GEN_PVAR_144 : A) (i : K) (u : type1223 A K) : (term822 A K GEN_PVAR_144 i u) = (term823 A K GEN_PVAR_144 i u).
Proof. exact (MK_COMB (@lem4474133 A) (@lem4474132 A K GEN_PVAR_144 i u)). Qed.
Lemma lem4474135 {A K : Type'} (i : K) (u : type1223 A K) : (term824 A K i u) = (term825 A K i u).
Proof. exact (fun_ext (fun GEN_PVAR_144 : A => @lem4474134 A K GEN_PVAR_144 i u)). Qed.
Lemma lem4474136 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4474137 {A K : Type'} (i : K) (u : type1223 A K) : (term826 A K i u) = (term663 A K i u).
Proof. exact (MK_COMB (@lem4474136 A) (@lem4474135 A K i u)). Qed.
Lemma lem4474138 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4474139 {A K : Type'} (x : A) (i : K) (u : type1223 A K) : (term813 A K x i u) = (term668 A K x i u).
Proof. exact (MK_COMB (@lem4474138 A x) (@lem4474137 A K i u)). Qed.
Lemma lem4474140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474141 {A K : Type'} (x : A) (i : K) (u : type1223 A K) : (term827 A K x i u) = (term828 A K x i u).
Proof. exact (MK_COMB (@lem4474140) (@lem4474139 A K x i u)). Qed.
Lemma lem4474142 {A K : Type'} (i : K) (x : A) (u : type1223 A K) : (term814 A K i u x) = (term748 A K i x u).
Proof. exact (eq_refl (term814 A K i u x)). Qed.
Lemma lem4474143 {A K : Type'} (i : K) (x : A) (u : type1223 A K) : ((term813 A K x i u) = (term814 A K i u x)) = ((term668 A K x i u) = (term748 A K i x u)).
Proof. exact (MK_COMB (@lem4474141 A K x i u) (@lem4474142 A K i x u)). Qed.
Lemma lem4474144 {A K : Type'} (i : K) (x : A) (u : type1223 A K) : (term668 A K x i u) = (term748 A K i x u).
Proof. exact (EQ_MP (@lem4474143 A K i x u) (@lem4474126 A K i u x)). Qed.
Lemma lem4474146 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474147 {A K : Type'} (P : type1223 A K) (x : prod K A) : (@IN (prod K A) x P) = (P x).
Proof. exact (@lem4474146 (prod K A) P x). Qed.
Lemma lem4474148 {A K : Type'} (u : type1223 A K) (i : K) (x : A) : (term748 A K i x u) = (term801 A K u i x).
Proof. exact (@lem4474147 A K u (@pair K A i x)). Qed.
Lemma lem4474149 {A K : Type'} (u : type1223 A K) (i : K) (x : A) : (term668 A K x i u) = (term801 A K u i x).
Proof. exact (TRANS (@lem4474144 A K i x u) (@lem4474148 A K u i x)). Qed.
Lemma lem4474150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4474151 {A K : Type'} (u : type1223 A K) (i : K) (x : A) : (term670 A K x i u) = (term802 A K u i x).
Proof. exact (MK_COMB (@lem4474150) (@lem4474149 A K u i x)). Qed.
Lemma lem4474153 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4474154 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4474153 A P x). Qed.
Lemma lem4474155 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term671 A K x s i) = (s i x).
Proof. exact (@lem4474154 A (s i) x). Qed.
Lemma lem4474156 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term673 A K u x s i) = (term836 A K u s i x).
Proof. exact (MK_COMB (@lem4474151 A K u i x) (@lem4474155 A K s i x)). Qed.
Lemma lem4474159 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term675 A K u s i) = (term837 A K u s i).
Proof. exact (fun_ext (fun x : A => @lem4474156 A K u s i x)). Qed.
Lemma lem4474160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474161 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term676 A K u s i) = (term838 A K u s i).
Proof. exact (MK_COMB (@lem4474160 A) (@lem4474159 A K u s i)). Qed.
Lemma lem4474166 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term679 A K k u s i) = (term839 A K k u s i).
Proof. exact (MK_COMB (@lem4474116 K k i) (@lem4474161 A K u s i)). Qed.
Lemma lem4474169 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term681 A K k u s) = (term840 A K k u s).
Proof. exact (fun_ext (fun i : K => @lem4474166 A K k u s i)). Qed.
Lemma lem4474170 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474171 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term683 A K k u s) = (term841 A K k u s).
Proof. exact (MK_COMB (@lem4474170 K) (@lem4474169 A K k u s)). Qed.
Lemma lem4474176 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term799 A K k u s) = (term842 A K k u s).
Proof. exact (MK_COMB (@lem4474104 A K k u) (@lem4474171 A K k u s)). Qed.
Lemma lem4474179 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term800 A K k u s) = (term843 A K k u s).
Proof. exact (MK_COMB (@lem4474029 A K u k s) (@lem4474176 A K k u s)). Qed.
Lemma lem4474182 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term843 A K k u s) = (term800 A K k u s).
Proof. exact (SYM (@lem4474179 A K k u s)). Qed.
Lemma lem4474184 (p : Prop) : p = (term22 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4474185 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term843 A K k u s) = (term844 A K k u s).
Proof. exact (@lem4474184 (term843 A K k u s)). Qed.
Lemma lem4474186 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term844 A K k u s) = (term843 A K k u s).
Proof. exact (SYM (@lem4474185 A K k u s)). Qed.
Lemma lem4474187 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term845 A K k u s) : term845 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474190 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term844 A K k u s) : term844 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474191 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term846 A K k u s.
Proof. exact (fun h0 : term844 A K k u s => @lem4474190 A K k u s h0). Qed.
Lemma lem4474192 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term846 A K k u s) : term846 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474193 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term844 A K k u s) : term844 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474194 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term844 A K k u s) (h2 : term846 A K k u s) : term844 A K k u s.
Proof. exact (@lem4474192 A K k u s h2 (@lem4474193 A K k u s h1)). Qed.
Lemma lem4474195 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term844 A K k u s) : term847 A K k u s.
Proof. exact (fun h0 : term846 A K k u s => @lem4474194 A K k u s h1 h0). Qed.
Lemma lem4474196 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term846 A K k u s) : term846 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474197 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term844 A K k u s) (h2 : term846 A K k u s) : term844 A K k u s.
Proof. exact (@lem4474195 A K k u s h1 (@lem4474196 A K k u s h2)). Qed.
Lemma lem4474198 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term846 A K k u s) : term846 A K k u s.
Proof. exact (fun h0 : term844 A K k u s => @lem4474197 A K k u s h0 h1). Qed.
Lemma lem4474199 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term848 A K k u s.
Proof. exact (fun h0 : term846 A K k u s => @lem4474198 A K k u s h0). Qed.
Lemma lem4474202 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term846 A K k u s.
Proof. exact (@lem4474199 A K k u s (@lem4474191 A K k u s)). Qed.
Lemma lem4474203 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term846 A K k u s.
Proof. exact (@lem4474202 A K k u s). Qed.
Lemma lem4474217 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4474218 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term844 A K k u s) = (term849 A K k u s).
Proof. exact (@lem4474217 (term845 A K k u s)). Qed.
Lemma lem4474220 (t : Prop) : (term629 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4474221 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term849 A K k u s) = (term843 A K k u s).
Proof. exact (@lem4474220 (term843 A K k u s)). Qed.
Lemma lem4474224 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term844 A K k u s) = (term843 A K k u s).
Proof. exact (TRANS (@lem4474218 A K k u s) (@lem4474221 A K k u s)). Qed.
Lemma lem4474261 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : (term850 A K u s) = (term851 A K u s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4474224 A K k u s)). Qed.
Lemma lem4474262 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4474263 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : (term852 A K u s) = (term853 A K u s).
Proof. exact (MK_COMB (@lem4474262 K) (@lem4474261 A K u s)). Qed.
Lemma lem4474268 {A K : Type'} (s : type1470 A K) : (term854 A K s) = (term855 A K s).
Proof. exact (fun_ext (fun u : type1223 A K => @lem4474263 A K u s)). Qed.
Lemma lem4474269 {A K : Type'} : (@all ((prod K A) -> Prop)) = (@all ((prod K A) -> Prop)).
Proof. exact (eq_refl (@all ((prod K A) -> Prop))). Qed.
Lemma lem4474270 {A K : Type'} (s : type1470 A K) : (term856 A K s) = (term857 A K s).
Proof. exact (MK_COMB (@lem4474269 A K) (@lem4474268 A K s)). Qed.
Lemma lem4474275 {A K : Type'} : (term858 A K) = (term859 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4474270 A K s)). Qed.
Lemma lem4474276 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4474285 {A K : Type'} : (term860 A K) = (term861 A K).
Proof. exact (MK_COMB (@lem4474276 A K) (@lem4474275 A K)). Qed.
Lemma lem4474290 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term836 A K u s i x) = (term836 A K u s i x).
Proof. exact (eq_refl (term836 A K u s i x)). Qed.
Lemma lem4474291 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term837 A K u s i) = (term837 A K u s i).
Proof. exact (fun_ext (fun x : A => @lem4474290 A K u s i x)). Qed.
Lemma lem4474292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474293 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term838 A K u s i) = (term838 A K u s i).
Proof. exact (MK_COMB (@lem4474292 A) (@lem4474291 A K u s i)). Qed.
Lemma lem4474296 {K : Type'} (k : K -> Prop) (i : K) : (term835 K k i) = (term835 K k i).
Proof. exact (eq_refl (term835 K k i)). Qed.
Lemma lem4474297 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term839 A K k u s i) = (term839 A K k u s i).
Proof. exact (MK_COMB (@lem4474296 K k i) (@lem4474293 A K u s i)). Qed.
Lemma lem4474298 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term840 A K k u s) = (term840 A K k u s).
Proof. exact (fun_ext (fun i : K => @lem4474297 A K k u s i)). Qed.
Lemma lem4474299 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474300 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term841 A K k u s) = (term841 A K k u s).
Proof. exact (MK_COMB (@lem4474299 K) (@lem4474298 A K k u s)). Qed.
Lemma lem4474309 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : ((term801 A K u p1 p2) = (term829 A K k u p1 p2)) = ((term801 A K u p1 p2) = (term829 A K k u p1 p2)).
Proof. exact (eq_refl ((term801 A K u p1 p2) = (term829 A K k u p1 p2))). Qed.
Lemma lem4474310 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term830 A K k u p1) = (term830 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474309 A K k u p1 p2)). Qed.
Lemma lem4474311 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474312 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term831 A K k u p1) = (term831 A K k u p1).
Proof. exact (MK_COMB (@lem4474311 A) (@lem4474310 A K k u p1)). Qed.
Lemma lem4474313 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term832 A K k u) = (term832 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474312 A K k u p1)). Qed.
Lemma lem4474314 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474315 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term833 A K k u) = (term833 A K k u).
Proof. exact (MK_COMB (@lem4474314 K) (@lem4474313 A K k u)). Qed.
Lemma lem4474316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4474317 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term834 A K k u) = (term834 A K k u).
Proof. exact (MK_COMB (@lem4474316) (@lem4474315 A K k u)). Qed.
Lemma lem4474318 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term842 A K k u s) = (term842 A K k u s).
Proof. exact (MK_COMB (@lem4474317 A K k u) (@lem4474300 A K k u s)). Qed.
Lemma lem4474327 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term805 A K u k s p1 p2) = (term805 A K u k s p1 p2).
Proof. exact (eq_refl (term805 A K u k s p1 p2)). Qed.
Lemma lem4474328 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term806 A K u k s p1) = (term806 A K u k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474327 A K u k s p1 p2)). Qed.
Lemma lem4474329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474330 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term807 A K u k s p1) = (term807 A K u k s p1).
Proof. exact (MK_COMB (@lem4474329 A) (@lem4474328 A K u k s p1)). Qed.
Lemma lem4474331 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term808 A K u k s) = (term808 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4474330 A K u k s p1)). Qed.
Lemma lem4474332 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474333 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term809 A K u k s) = (term809 A K u k s).
Proof. exact (MK_COMB (@lem4474332 K) (@lem4474331 A K u k s)). Qed.
Lemma lem4474334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4474335 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term810 A K u k s) = (term810 A K u k s).
Proof. exact (MK_COMB (@lem4474334) (@lem4474333 A K u k s)). Qed.
Lemma lem4474336 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term843 A K k u s) = (term843 A K k u s).
Proof. exact (MK_COMB (@lem4474335 A K u k s) (@lem4474318 A K k u s)). Qed.
Lemma lem4474337 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : (term851 A K u s) = (term851 A K u s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4474336 A K k u s)). Qed.
Lemma lem4474338 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4474339 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : (term853 A K u s) = (term853 A K u s).
Proof. exact (MK_COMB (@lem4474338 K) (@lem4474337 A K u s)). Qed.
Lemma lem4474340 {A K : Type'} (s : type1470 A K) : (term855 A K s) = (term855 A K s).
Proof. exact (fun_ext (fun u : type1223 A K => @lem4474339 A K u s)). Qed.
Lemma lem4474341 {A K : Type'} : (@all ((prod K A) -> Prop)) = (@all ((prod K A) -> Prop)).
Proof. exact (eq_refl (@all ((prod K A) -> Prop))). Qed.
Lemma lem4474342 {A K : Type'} (s : type1470 A K) : (term857 A K s) = (term857 A K s).
Proof. exact (MK_COMB (@lem4474341 A K) (@lem4474340 A K s)). Qed.
Lemma lem4474343 {A K : Type'} : (term859 A K) = (term859 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4474342 A K s)). Qed.
Lemma lem4474344 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4474345 {A K : Type'} : (term861 A K) = (term861 A K).
Proof. exact (MK_COMB (@lem4474344 A K) (@lem4474343 A K)). Qed.
Lemma lem4474416 {A K : Type'} : (term860 A K) = (term861 A K).
Proof. exact (TRANS (@lem4474285 A K) (@lem4474345 A K)). Qed.
Lemma lem4474417 {A K : Type'} : (term861 A K) = (term860 A K).
Proof. exact (SYM (@lem4474416 A K)). Qed.
Lemma lem4474418 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term809 A K u k s.
Proof. exact (h1). Qed.
Lemma lem4474420 (p : Prop) : p = (term22 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4474421 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term842 A K k u s) = (term862 A K k u s).
Proof. exact (@lem4474420 (term842 A K k u s)). Qed.
Lemma lem4474422 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term862 A K k u s) = (term842 A K k u s).
Proof. exact (SYM (@lem4474421 A K k u s)). Qed.
Lemma lem4474423 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term863 A K k u s) : term863 A K k u s.
Proof. exact (h1). Qed.
Lemma lem4474434 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term805 A K u k s p1 p2) = (term864 A K u k s p1 p2).
Proof. exact (@lem17265 (term801 A K u p1 p2) (term804 A K k s p1 p2)). Qed.
Lemma lem4474435 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term806 A K u k s p1) = (term865 A K u k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474434 A K u k s p1 p2)). Qed.
Lemma lem4474436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4474437 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term807 A K u k s p1) = (term866 A K u k s p1).
Proof. exact (MK_COMB (@lem4474436 A) (@lem4474435 A K u k s p1)). Qed.
Lemma lem4474438 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term808 A K u k s) = (term867 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4474437 A K u k s p1)). Qed.
Lemma lem4474439 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4474496 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term809 A K u k s) = (term868 A K u k s).
Proof. exact (MK_COMB (@lem4474439 K) (@lem4474438 A K u k s)). Qed.
Lemma lem4474497 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term868 A K u k s.
Proof. exact (EQ_MP (@lem4474496 A K u k s) (@lem4474418 A K u k s h1)). Qed.
Lemma lem4474508 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term869 A K k u p1 p2) = (term870 A K k u p1 p2).
Proof. exact (@lem17045 (k p1) (term801 A K u p1 p2)). Qed.
Lemma lem4474514 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term871 A K k u p1 p2) = (term871 A K k u p1 p2).
Proof. exact (eq_refl (term871 A K k u p1 p2)). Qed.
Lemma lem4474516 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term872 A K u p1 p2) = (term872 A K u p1 p2).
Proof. exact (eq_refl (term872 A K u p1 p2)). Qed.
Lemma lem4474517 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term873 A K k u p1 p2) = (term874 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474516 A K u p1 p2) (@lem4474508 A K k u p1 p2)). Qed.
Lemma lem4474518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474519 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term875 A K k u p1 p2) = (term876 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474518) (@lem4474517 A K k u p1 p2)). Qed.
Lemma lem4474520 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term877 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474519 A K k u p1 p2) (@lem4474514 A K k u p1 p2)). Qed.
Lemma lem4474521 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term879 A K k u p1 p2) = (term877 A K k u p1 p2).
Proof. exact (@lem17646 (term801 A K u p1 p2) (term829 A K k u p1 p2)). Qed.
Lemma lem4474522 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term879 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (TRANS (@lem4474521 A K k u p1 p2) (@lem4474520 A K k u p1 p2)). Qed.
Lemma lem4474523 {A : Type'} (P : A -> Prop) : (term109 A P) = (term110 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4474524 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term880 A K k u p1) = (term881 A K k u p1).
Proof. exact (@lem4474523 A (term830 A K k u p1)). Qed.
Lemma lem4474525 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term882 A K k u p1 p2) = ((term801 A K u p1 p2) = (term829 A K k u p1 p2)).
Proof. exact (eq_refl (term882 A K k u p1 p2)). Qed.
Lemma lem4474526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4474527 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term883 A K k u p1 p2) = (term879 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474526) (@lem4474525 A K k u p1 p2)). Qed.
Lemma lem4474528 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term883 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (TRANS (@lem4474527 A K k u p1 p2) (@lem4474522 A K k u p1 p2)). Qed.
Lemma lem4474529 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term884 A K k u p1) = (term885 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474528 A K k u p1 p2)). Qed.
Lemma lem4474530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474531 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term881 A K k u p1) = (term886 A K k u p1).
Proof. exact (MK_COMB (@lem4474530 A) (@lem4474529 A K k u p1)). Qed.
Lemma lem4474532 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term880 A K k u p1) = (term886 A K k u p1).
Proof. exact (TRANS (@lem4474524 A K k u p1) (@lem4474531 A K k u p1)). Qed.
Lemma lem4474533 {K : Type'} (P : K -> Prop) : (term109 K P) = (term110 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4474534 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term887 A K k u) = (term888 A K k u).
Proof. exact (@lem4474533 K (term832 A K k u)). Qed.
Lemma lem4474535 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term889 A K k u p1) = (term831 A K k u p1).
Proof. exact (eq_refl (term889 A K k u p1)). Qed.
Lemma lem4474536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4474537 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term890 A K k u p1) = (term880 A K k u p1).
Proof. exact (MK_COMB (@lem4474536) (@lem4474535 A K k u p1)). Qed.
Lemma lem4474538 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term890 A K k u p1) = (term886 A K k u p1).
Proof. exact (TRANS (@lem4474537 A K k u p1) (@lem4474532 A K k u p1)). Qed.
Lemma lem4474539 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term891 A K k u) = (term892 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474538 A K k u p1)). Qed.
Lemma lem4474540 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474541 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term888 A K k u) = (term893 A K k u).
Proof. exact (MK_COMB (@lem4474540 K) (@lem4474539 A K k u)). Qed.
Lemma lem4474542 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term887 A K k u) = (term893 A K k u).
Proof. exact (TRANS (@lem4474534 A K k u) (@lem4474541 A K k u)). Qed.
Lemma lem4474550 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term894 A K u s i x) = (term895 A K u s i x).
Proof. exact (@lem17362 (term801 A K u i x) (s i x)). Qed.
Lemma lem4474551 {A : Type'} (P : A -> Prop) : (term109 A P) = (term110 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4474552 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term896 A K u s i) = (term897 A K u s i).
Proof. exact (@lem4474551 A (term837 A K u s i)). Qed.
Lemma lem4474553 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term898 A K u s i x) = (term836 A K u s i x).
Proof. exact (eq_refl (term898 A K u s i x)). Qed.
Lemma lem4474554 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4474555 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term899 A K u s i x) = (term894 A K u s i x).
Proof. exact (MK_COMB (@lem4474554) (@lem4474553 A K u s i x)). Qed.
Lemma lem4474556 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term899 A K u s i x) = (term895 A K u s i x).
Proof. exact (TRANS (@lem4474555 A K u s i x) (@lem4474550 A K u s i x)). Qed.
Lemma lem4474557 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term900 A K u s i) = (term901 A K u s i).
Proof. exact (fun_ext (fun x : A => @lem4474556 A K u s i x)). Qed.
Lemma lem4474558 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474559 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term897 A K u s i) = (term902 A K u s i).
Proof. exact (MK_COMB (@lem4474558 A) (@lem4474557 A K u s i)). Qed.
Lemma lem4474560 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term896 A K u s i) = (term902 A K u s i).
Proof. exact (TRANS (@lem4474552 A K u s i) (@lem4474559 A K u s i)). Qed.
Lemma lem4474562 {K : Type'} (k : K -> Prop) (i : K) : (term803 K k i) = (term803 K k i).
Proof. exact (eq_refl (term803 K k i)). Qed.
Lemma lem4474563 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term903 A K k u s i) = (term904 A K k u s i).
Proof. exact (MK_COMB (@lem4474562 K k i) (@lem4474560 A K u s i)). Qed.
Lemma lem4474564 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term905 A K k u s i) = (term903 A K k u s i).
Proof. exact (@lem17362 (k i) (term838 A K u s i)). Qed.
Lemma lem4474565 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term905 A K k u s i) = (term904 A K k u s i).
Proof. exact (TRANS (@lem4474564 A K k u s i) (@lem4474563 A K k u s i)). Qed.
Lemma lem4474566 {K : Type'} (P : K -> Prop) : (term109 K P) = (term110 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4474567 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term906 A K k u s) = (term907 A K k u s).
Proof. exact (@lem4474566 K (term840 A K k u s)). Qed.
Lemma lem4474568 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term908 A K k u s i) = (term839 A K k u s i).
Proof. exact (eq_refl (term908 A K k u s i)). Qed.
Lemma lem4474569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4474570 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term909 A K k u s i) = (term905 A K k u s i).
Proof. exact (MK_COMB (@lem4474569) (@lem4474568 A K k u s i)). Qed.
Lemma lem4474571 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term909 A K k u s i) = (term904 A K k u s i).
Proof. exact (TRANS (@lem4474570 A K k u s i) (@lem4474565 A K k u s i)). Qed.
Lemma lem4474572 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term910 A K k u s) = (term911 A K k u s).
Proof. exact (fun_ext (fun i : K => @lem4474571 A K k u s i)). Qed.
Lemma lem4474573 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474574 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term907 A K k u s) = (term912 A K k u s).
Proof. exact (MK_COMB (@lem4474573 K) (@lem4474572 A K k u s)). Qed.
Lemma lem4474575 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term906 A K k u s) = (term912 A K k u s).
Proof. exact (TRANS (@lem4474567 A K k u s) (@lem4474574 A K k u s)). Qed.
Lemma lem4474576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474577 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term913 A K k u) = (term914 A K k u).
Proof. exact (MK_COMB (@lem4474576) (@lem4474542 A K k u)). Qed.
Lemma lem4474578 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term915 A K k u s) = (term916 A K k u s).
Proof. exact (MK_COMB (@lem4474577 A K k u) (@lem4474575 A K k u s)). Qed.
Lemma lem4474579 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term863 A K k u s) = (term915 A K k u s).
Proof. exact (@lem17045 (term833 A K k u) (term841 A K k u s)). Qed.
Lemma lem4474580 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term863 A K k u s) = (term916 A K k u s).
Proof. exact (TRANS (@lem4474579 A K k u s) (@lem4474578 A K k u s)). Qed.
Lemma lem4474586 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term917 A P Q) = (term918 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4474587 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term917 A P Q) = (term918 A P Q).
Proof. exact (@lem4474586 A P Q). Qed.
Lemma lem4474588 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term919 A K k u p1) = (term920 A K k u p1).
Proof. exact (@lem4474587 A (term921 A K k u p1) (term922 A K k u p1)). Qed.
Lemma lem4474589 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term923 A K k u p1 p2) = (term874 A K k u p1 p2).
Proof. exact (eq_refl (term923 A K k u p1 p2)). Qed.
Lemma lem4474590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474591 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term924 A K k u p1 p2) = (term876 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474590) (@lem4474589 A K k u p1 p2)). Qed.
Lemma lem4474592 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term925 A K k u p1 p2) = (term871 A K k u p1 p2).
Proof. exact (eq_refl (term925 A K k u p1 p2)). Qed.
Lemma lem4474593 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term926 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474591 A K k u p1 p2) (@lem4474592 A K k u p1 p2)). Qed.
Lemma lem4474594 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term927 A K k u p1) = (term885 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474593 A K k u p1 p2)). Qed.
Lemma lem4474595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474596 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term919 A K k u p1) = (term886 A K k u p1).
Proof. exact (MK_COMB (@lem4474595 A) (@lem4474594 A K k u p1)). Qed.
Lemma lem4474597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474598 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term928 A K k u p1) = (term929 A K k u p1).
Proof. exact (MK_COMB (@lem4474597) (@lem4474596 A K k u p1)). Qed.
Lemma lem4474599 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term923 A K k u p1 p2) = (term874 A K k u p1 p2).
Proof. exact (eq_refl (term923 A K k u p1 p2)). Qed.
Lemma lem4474600 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term930 A K k u p1) = (term921 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474599 A K k u p1 p2)). Qed.
Lemma lem4474601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474602 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term931 A K k u p1) = (term932 A K k u p1).
Proof. exact (MK_COMB (@lem4474601 A) (@lem4474600 A K k u p1)). Qed.
Lemma lem4474603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474604 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term933 A K k u p1) = (term934 A K k u p1).
Proof. exact (MK_COMB (@lem4474603) (@lem4474602 A K k u p1)). Qed.
Lemma lem4474605 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term925 A K k u p1 p2) = (term871 A K k u p1 p2).
Proof. exact (eq_refl (term925 A K k u p1 p2)). Qed.
Lemma lem4474606 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term935 A K k u p1) = (term922 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474605 A K k u p1 p2)). Qed.
Lemma lem4474607 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474608 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term936 A K k u p1) = (term937 A K k u p1).
Proof. exact (MK_COMB (@lem4474607 A) (@lem4474606 A K k u p1)). Qed.
Lemma lem4474609 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term920 A K k u p1) = (term938 A K k u p1).
Proof. exact (MK_COMB (@lem4474604 A K k u p1) (@lem4474608 A K k u p1)). Qed.
Lemma lem4474610 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : ((term919 A K k u p1) = (term920 A K k u p1)) = ((term886 A K k u p1) = (term938 A K k u p1)).
Proof. exact (MK_COMB (@lem4474598 A K k u p1) (@lem4474609 A K k u p1)). Qed.
Lemma lem4474611 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term886 A K k u p1) = (term938 A K k u p1).
Proof. exact (EQ_MP (@lem4474610 A K k u p1) (@lem4474588 A K k u p1)). Qed.
Lemma lem4474708 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term892 A K k u) = (term939 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474611 A K k u p1)). Qed.
Lemma lem4474709 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474710 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term893 A K k u) = (term940 A K k u).
Proof. exact (MK_COMB (@lem4474709 K) (@lem4474708 A K k u)). Qed.
Lemma lem4474712 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term917 A P Q) = (term918 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4474713 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term917 K P Q) = (term918 K P Q).
Proof. exact (@lem4474712 K P Q). Qed.
Lemma lem4474714 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term941 A K k u) = (term942 A K k u).
Proof. exact (@lem4474713 K (term943 A K k u) (term944 A K k u)). Qed.
Lemma lem4474715 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term945 A K k u p1) = (term932 A K k u p1).
Proof. exact (eq_refl (term945 A K k u p1)). Qed.
Lemma lem4474716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474717 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term946 A K k u p1) = (term934 A K k u p1).
Proof. exact (MK_COMB (@lem4474716) (@lem4474715 A K k u p1)). Qed.
Lemma lem4474718 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term947 A K k u p1) = (term937 A K k u p1).
Proof. exact (eq_refl (term947 A K k u p1)). Qed.
Lemma lem4474719 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term948 A K k u p1) = (term938 A K k u p1).
Proof. exact (MK_COMB (@lem4474717 A K k u p1) (@lem4474718 A K k u p1)). Qed.
Lemma lem4474720 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term949 A K k u) = (term939 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474719 A K k u p1)). Qed.
Lemma lem4474721 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474722 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term941 A K k u) = (term940 A K k u).
Proof. exact (MK_COMB (@lem4474721 K) (@lem4474720 A K k u)). Qed.
Lemma lem4474723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474724 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term950 A K k u) = (term951 A K k u).
Proof. exact (MK_COMB (@lem4474723) (@lem4474722 A K k u)). Qed.
Lemma lem4474725 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term945 A K k u p1) = (term932 A K k u p1).
Proof. exact (eq_refl (term945 A K k u p1)). Qed.
Lemma lem4474726 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term952 A K k u) = (term943 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474725 A K k u p1)). Qed.
Lemma lem4474727 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474728 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term953 A K k u) = (term954 A K k u).
Proof. exact (MK_COMB (@lem4474727 K) (@lem4474726 A K k u)). Qed.
Lemma lem4474729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474730 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term955 A K k u) = (term956 A K k u).
Proof. exact (MK_COMB (@lem4474729) (@lem4474728 A K k u)). Qed.
Lemma lem4474731 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term947 A K k u p1) = (term937 A K k u p1).
Proof. exact (eq_refl (term947 A K k u p1)). Qed.
Lemma lem4474732 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term957 A K k u) = (term944 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474731 A K k u p1)). Qed.
Lemma lem4474733 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474734 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term958 A K k u) = (term959 A K k u).
Proof. exact (MK_COMB (@lem4474733 K) (@lem4474732 A K k u)). Qed.
Lemma lem4474735 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term942 A K k u) = (term960 A K k u).
Proof. exact (MK_COMB (@lem4474730 A K k u) (@lem4474734 A K k u)). Qed.
Lemma lem4474736 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : ((term941 A K k u) = (term942 A K k u)) = ((term940 A K k u) = (term960 A K k u)).
Proof. exact (MK_COMB (@lem4474724 A K k u) (@lem4474735 A K k u)). Qed.
Lemma lem4474737 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term940 A K k u) = (term960 A K k u).
Proof. exact (EQ_MP (@lem4474736 A K k u) (@lem4474714 A K k u)). Qed.
Lemma lem4474842 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term893 A K k u) = (term960 A K k u).
Proof. exact (TRANS (@lem4474710 A K k u) (@lem4474737 A K k u)). Qed.
Lemma lem4474843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474844 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term914 A K k u) = (term961 A K k u).
Proof. exact (MK_COMB (@lem4474843) (@lem4474842 A K k u)). Qed.
Lemma lem4474921 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term912 A K k u s) = (term912 A K k u s).
Proof. exact (eq_refl (term912 A K k u s)). Qed.
Lemma lem4474922 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term916 A K k u s) = (term962 A K k u s).
Proof. exact (MK_COMB (@lem4474844 A K k u) (@lem4474921 A K k u s)). Qed.
Lemma lem4474924 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4474925 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term918 K P Q) = (term917 K P Q).
Proof. exact (@lem4474924 K P Q). Qed.
Lemma lem4474926 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term942 A K k u) = (term941 A K k u).
Proof. exact (@lem4474925 K (term943 A K k u) (term944 A K k u)). Qed.
Lemma lem4474927 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term945 A K k u p1) = (term932 A K k u p1).
Proof. exact (eq_refl (term945 A K k u p1)). Qed.
Lemma lem4474928 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term952 A K k u) = (term943 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474927 A K k u p1)). Qed.
Lemma lem4474929 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474930 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term953 A K k u) = (term954 A K k u).
Proof. exact (MK_COMB (@lem4474929 K) (@lem4474928 A K k u)). Qed.
Lemma lem4474931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474932 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term955 A K k u) = (term956 A K k u).
Proof. exact (MK_COMB (@lem4474931) (@lem4474930 A K k u)). Qed.
Lemma lem4474933 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term947 A K k u p1) = (term937 A K k u p1).
Proof. exact (eq_refl (term947 A K k u p1)). Qed.
Lemma lem4474934 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term957 A K k u) = (term944 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474933 A K k u p1)). Qed.
Lemma lem4474935 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474936 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term958 A K k u) = (term959 A K k u).
Proof. exact (MK_COMB (@lem4474935 K) (@lem4474934 A K k u)). Qed.
Lemma lem4474937 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term942 A K k u) = (term960 A K k u).
Proof. exact (MK_COMB (@lem4474932 A K k u) (@lem4474936 A K k u)). Qed.
Lemma lem4474938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474939 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term963 A K k u) = (term964 A K k u).
Proof. exact (MK_COMB (@lem4474938) (@lem4474937 A K k u)). Qed.
Lemma lem4474940 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term945 A K k u p1) = (term932 A K k u p1).
Proof. exact (eq_refl (term945 A K k u p1)). Qed.
Lemma lem4474941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474942 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term946 A K k u p1) = (term934 A K k u p1).
Proof. exact (MK_COMB (@lem4474941) (@lem4474940 A K k u p1)). Qed.
Lemma lem4474943 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term947 A K k u p1) = (term937 A K k u p1).
Proof. exact (eq_refl (term947 A K k u p1)). Qed.
Lemma lem4474944 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term948 A K k u p1) = (term938 A K k u p1).
Proof. exact (MK_COMB (@lem4474942 A K k u p1) (@lem4474943 A K k u p1)). Qed.
Lemma lem4474945 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term949 A K k u) = (term939 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474944 A K k u p1)). Qed.
Lemma lem4474946 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474947 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term941 A K k u) = (term940 A K k u).
Proof. exact (MK_COMB (@lem4474946 K) (@lem4474945 A K k u)). Qed.
Lemma lem4474948 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : ((term942 A K k u) = (term941 A K k u)) = ((term960 A K k u) = (term940 A K k u)).
Proof. exact (MK_COMB (@lem4474939 A K k u) (@lem4474947 A K k u)). Qed.
Lemma lem4474949 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term960 A K k u) = (term940 A K k u).
Proof. exact (EQ_MP (@lem4474948 A K k u) (@lem4474926 A K k u)). Qed.
Lemma lem4474951 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4474952 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (@lem4474951 A P Q). Qed.
Lemma lem4474953 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term920 A K k u p1) = (term919 A K k u p1).
Proof. exact (@lem4474952 A (term921 A K k u p1) (term922 A K k u p1)). Qed.
Lemma lem4474954 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term923 A K k u p1 p2) = (term874 A K k u p1 p2).
Proof. exact (eq_refl (term923 A K k u p1 p2)). Qed.
Lemma lem4474955 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term930 A K k u p1) = (term921 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474954 A K k u p1 p2)). Qed.
Lemma lem4474956 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474957 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term931 A K k u p1) = (term932 A K k u p1).
Proof. exact (MK_COMB (@lem4474956 A) (@lem4474955 A K k u p1)). Qed.
Lemma lem4474958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474959 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term933 A K k u p1) = (term934 A K k u p1).
Proof. exact (MK_COMB (@lem4474958) (@lem4474957 A K k u p1)). Qed.
Lemma lem4474960 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term925 A K k u p1 p2) = (term871 A K k u p1 p2).
Proof. exact (eq_refl (term925 A K k u p1 p2)). Qed.
Lemma lem4474961 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term935 A K k u p1) = (term922 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474960 A K k u p1 p2)). Qed.
Lemma lem4474962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474963 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term936 A K k u p1) = (term937 A K k u p1).
Proof. exact (MK_COMB (@lem4474962 A) (@lem4474961 A K k u p1)). Qed.
Lemma lem4474964 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term920 A K k u p1) = (term938 A K k u p1).
Proof. exact (MK_COMB (@lem4474959 A K k u p1) (@lem4474963 A K k u p1)). Qed.
Lemma lem4474965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474966 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term965 A K k u p1) = (term966 A K k u p1).
Proof. exact (MK_COMB (@lem4474965) (@lem4474964 A K k u p1)). Qed.
Lemma lem4474967 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term923 A K k u p1 p2) = (term874 A K k u p1 p2).
Proof. exact (eq_refl (term923 A K k u p1 p2)). Qed.
Lemma lem4474968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474969 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term924 A K k u p1 p2) = (term876 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474968) (@lem4474967 A K k u p1 p2)). Qed.
Lemma lem4474970 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term925 A K k u p1 p2) = (term871 A K k u p1 p2).
Proof. exact (eq_refl (term925 A K k u p1 p2)). Qed.
Lemma lem4474971 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term926 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4474969 A K k u p1 p2) (@lem4474970 A K k u p1 p2)). Qed.
Lemma lem4474972 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term927 A K k u p1) = (term885 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4474971 A K k u p1 p2)). Qed.
Lemma lem4474973 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474974 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term919 A K k u p1) = (term886 A K k u p1).
Proof. exact (MK_COMB (@lem4474973 A) (@lem4474972 A K k u p1)). Qed.
Lemma lem4474975 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : ((term920 A K k u p1) = (term919 A K k u p1)) = ((term938 A K k u p1) = (term886 A K k u p1)).
Proof. exact (MK_COMB (@lem4474966 A K k u p1) (@lem4474974 A K k u p1)). Qed.
Lemma lem4474976 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term938 A K k u p1) = (term886 A K k u p1).
Proof. exact (EQ_MP (@lem4474975 A K k u p1) (@lem4474953 A K k u p1)). Qed.
Lemma lem4474977 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term939 A K k u) = (term892 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4474976 A K k u p1)). Qed.
Lemma lem4474978 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4474979 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term940 A K k u) = (term893 A K k u).
Proof. exact (MK_COMB (@lem4474978 K) (@lem4474977 A K k u)). Qed.
Lemma lem4474980 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term960 A K k u) = (term893 A K k u).
Proof. exact (TRANS (@lem4474949 A K k u) (@lem4474979 A K k u)). Qed.
Lemma lem4474981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4474982 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term961 A K k u) = (term914 A K k u).
Proof. exact (MK_COMB (@lem4474981) (@lem4474980 A K k u)). Qed.
Lemma lem4474984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term967 A P Q) = (term968 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4474985 {A : Type'} (P : Prop) (Q : A -> Prop) : (term967 A P Q) = (term968 A P Q).
Proof. exact (@lem4474984 A P Q). Qed.
Lemma lem4474986 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term969 A K k u s i) = (term970 A K k u s i).
Proof. exact (@lem4474985 A (k i) (term901 A K u s i)). Qed.
Lemma lem4474987 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term971 A K u s i x) = (term895 A K u s i x).
Proof. exact (eq_refl (term971 A K u s i x)). Qed.
Lemma lem4474988 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term972 A K u s i) = (term901 A K u s i).
Proof. exact (fun_ext (fun x : A => @lem4474987 A K u s i x)). Qed.
Lemma lem4474989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4474990 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) : (term973 A K u s i) = (term902 A K u s i).
Proof. exact (MK_COMB (@lem4474989 A) (@lem4474988 A K u s i)). Qed.
Lemma lem4474991 {K : Type'} (k : K -> Prop) (i : K) : (term803 K k i) = (term803 K k i).
Proof. exact (eq_refl (term803 K k i)). Qed.
Lemma lem4474992 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term969 A K k u s i) = (term904 A K k u s i).
Proof. exact (MK_COMB (@lem4474991 K k i) (@lem4474990 A K u s i)). Qed.
Lemma lem4474993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4474994 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term974 A K k u s i) = (term975 A K k u s i).
Proof. exact (MK_COMB (@lem4474993) (@lem4474992 A K k u s i)). Qed.
Lemma lem4474995 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term971 A K u s i x) = (term895 A K u s i x).
Proof. exact (eq_refl (term971 A K u s i x)). Qed.
Lemma lem4474996 {K : Type'} (k : K -> Prop) (i : K) : (term803 K k i) = (term803 K k i).
Proof. exact (eq_refl (term803 K k i)). Qed.
Lemma lem4474997 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) (x : A) : (term976 A K k u s i x) = (term977 A K k u s i x).
Proof. exact (MK_COMB (@lem4474996 K k i) (@lem4474995 A K u s i x)). Qed.
Lemma lem4474998 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term978 A K k u s i) = (term979 A K k u s i).
Proof. exact (fun_ext (fun x : A => @lem4474997 A K k u s i x)). Qed.
Lemma lem4474999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4475000 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term970 A K k u s i) = (term980 A K k u s i).
Proof. exact (MK_COMB (@lem4474999 A) (@lem4474998 A K k u s i)). Qed.
Lemma lem4475001 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : ((term969 A K k u s i) = (term970 A K k u s i)) = ((term904 A K k u s i) = (term980 A K k u s i)).
Proof. exact (MK_COMB (@lem4474994 A K k u s i) (@lem4475000 A K k u s i)). Qed.
Lemma lem4475002 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (i : K) : (term904 A K k u s i) = (term980 A K k u s i).
Proof. exact (EQ_MP (@lem4475001 A K k u s i) (@lem4474986 A K k u s i)). Qed.
Lemma lem4475003 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term911 A K k u s) = (term981 A K k u s).
Proof. exact (fun_ext (fun i : K => @lem4475002 A K k u s i)). Qed.
Lemma lem4475004 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475005 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term912 A K k u s) = (term982 A K k u s).
Proof. exact (MK_COMB (@lem4475004 K) (@lem4475003 A K k u s)). Qed.
Lemma lem4475006 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term962 A K k u s) = (term983 A K k u s).
Proof. exact (MK_COMB (@lem4474982 A K k u) (@lem4475005 A K k u s)). Qed.
Lemma lem4475008 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4475009 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term918 K P Q) = (term917 K P Q).
Proof. exact (@lem4475008 K P Q). Qed.
Lemma lem4475010 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term984 A K k u s) = (term985 A K k u s).
Proof. exact (@lem4475009 K (term892 A K k u) (term981 A K k u s)). Qed.
Lemma lem4475011 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term986 A K k u p1) = (term886 A K k u p1).
Proof. exact (eq_refl (term986 A K k u p1)). Qed.
Lemma lem4475012 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term987 A K k u) = (term892 A K k u).
Proof. exact (fun_ext (fun p1 : K => @lem4475011 A K k u p1)). Qed.
Lemma lem4475013 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475014 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term988 A K k u) = (term893 A K k u).
Proof. exact (MK_COMB (@lem4475013 K) (@lem4475012 A K k u)). Qed.
Lemma lem4475015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4475016 {A K : Type'} (k : K -> Prop) (u : type1223 A K) : (term989 A K k u) = (term914 A K k u).
Proof. exact (MK_COMB (@lem4475015) (@lem4475014 A K k u)). Qed.
Lemma lem4475017 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term990 A K k u s p1) = (term980 A K k u s p1).
Proof. exact (eq_refl (term990 A K k u s p1)). Qed.
Lemma lem4475018 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term991 A K k u s) = (term981 A K k u s).
Proof. exact (fun_ext (fun p1 : K => @lem4475017 A K k u s p1)). Qed.
Lemma lem4475019 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475020 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term992 A K k u s) = (term982 A K k u s).
Proof. exact (MK_COMB (@lem4475019 K) (@lem4475018 A K k u s)). Qed.
Lemma lem4475021 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term984 A K k u s) = (term983 A K k u s).
Proof. exact (MK_COMB (@lem4475016 A K k u) (@lem4475020 A K k u s)). Qed.
Lemma lem4475022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475023 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term993 A K k u s) = (term994 A K k u s).
Proof. exact (MK_COMB (@lem4475022) (@lem4475021 A K k u s)). Qed.
Lemma lem4475024 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term986 A K k u p1) = (term886 A K k u p1).
Proof. exact (eq_refl (term986 A K k u p1)). Qed.
Lemma lem4475025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4475026 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term995 A K k u p1) = (term996 A K k u p1).
Proof. exact (MK_COMB (@lem4475025) (@lem4475024 A K k u p1)). Qed.
Lemma lem4475027 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term990 A K k u s p1) = (term980 A K k u s p1).
Proof. exact (eq_refl (term990 A K k u s p1)). Qed.
Lemma lem4475028 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term997 A K k u s p1) = (term998 A K k u s p1).
Proof. exact (MK_COMB (@lem4475026 A K k u p1) (@lem4475027 A K k u s p1)). Qed.
Lemma lem4475029 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term999 A K k u s) = (term1000 A K k u s).
Proof. exact (fun_ext (fun p1 : K => @lem4475028 A K k u s p1)). Qed.
Lemma lem4475030 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475031 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term985 A K k u s) = (term1001 A K k u s).
Proof. exact (MK_COMB (@lem4475030 K) (@lem4475029 A K k u s)). Qed.
Lemma lem4475032 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term984 A K k u s) = (term985 A K k u s)) = ((term983 A K k u s) = (term1001 A K k u s)).
Proof. exact (MK_COMB (@lem4475023 A K k u s) (@lem4475031 A K k u s)). Qed.
Lemma lem4475033 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term983 A K k u s) = (term1001 A K k u s).
Proof. exact (EQ_MP (@lem4475032 A K k u s) (@lem4475010 A K k u s)). Qed.
Lemma lem4475036 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1002 A K k u s) = (term1002 A K k u s).
Proof. exact (eq_refl (term1002 A K k u s)). Qed.
Lemma lem4475037 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1002 A K k u s) = ((term983 A K k u s) = (term1001 A K k u s)).
Proof. exact (eq_refl (term1002 A K k u s)). Qed.
Lemma lem4475038 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1003 A K k u s) = (term1003 A K k u s).
Proof. exact (eq_refl (term1003 A K k u s)). Qed.
Lemma lem4475039 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term1002 A K k u s) = (term1002 A K k u s)) = ((term1002 A K k u s) = ((term983 A K k u s) = (term1001 A K k u s))).
Proof. exact (MK_COMB (@lem4475038 A K k u s) (@lem4475037 A K k u s)). Qed.
Lemma lem4475040 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1002 A K k u s) = ((term983 A K k u s) = (term1001 A K k u s)).
Proof. exact (eq_refl (term1002 A K k u s)). Qed.
Lemma lem4475041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475042 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1003 A K k u s) = (term1004 A K k u s).
Proof. exact (MK_COMB (@lem4475041) (@lem4475040 A K k u s)). Qed.
Lemma lem4475043 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term983 A K k u s) = (term1001 A K k u s)) = ((term983 A K k u s) = (term1001 A K k u s)).
Proof. exact (eq_refl ((term983 A K k u s) = (term1001 A K k u s))). Qed.
Lemma lem4475044 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term1002 A K k u s) = ((term983 A K k u s) = (term1001 A K k u s))) = (((term983 A K k u s) = (term1001 A K k u s)) = ((term983 A K k u s) = (term1001 A K k u s))).
Proof. exact (MK_COMB (@lem4475042 A K k u s) (@lem4475043 A K k u s)). Qed.
Lemma lem4475045 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term1002 A K k u s) = (term1002 A K k u s)) = (((term983 A K k u s) = (term1001 A K k u s)) = ((term983 A K k u s) = (term1001 A K k u s))).
Proof. exact (TRANS (@lem4475039 A K k u s) (@lem4475044 A K k u s)). Qed.
Lemma lem4475046 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : ((term983 A K k u s) = (term1001 A K k u s)) = ((term983 A K k u s) = (term1001 A K k u s)).
Proof. exact (EQ_MP (@lem4475045 A K k u s) (@lem4475036 A K k u s)). Qed.
Lemma lem4475047 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term983 A K k u s) = (term1001 A K k u s).
Proof. exact (EQ_MP (@lem4475046 A K k u s) (@lem4475033 A K k u s)). Qed.
Lemma lem4475049 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4475050 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term918 A P Q) = (term917 A P Q).
Proof. exact (@lem4475049 A P Q). Qed.
Lemma lem4475051 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1005 A K k u s p1) = (term1006 A K k u s p1).
Proof. exact (@lem4475050 A (term885 A K k u p1) (term979 A K k u s p1)). Qed.
Lemma lem4475052 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term1007 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (eq_refl (term1007 A K k u p1 p2)). Qed.
Lemma lem4475053 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term1008 A K k u p1) = (term885 A K k u p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475052 A K k u p1 p2)). Qed.
Lemma lem4475054 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4475055 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term1009 A K k u p1) = (term886 A K k u p1).
Proof. exact (MK_COMB (@lem4475054 A) (@lem4475053 A K k u p1)). Qed.
Lemma lem4475056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4475057 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) : (term1010 A K k u p1) = (term996 A K k u p1).
Proof. exact (MK_COMB (@lem4475056) (@lem4475055 A K k u p1)). Qed.
Lemma lem4475058 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) : (term1011 A K k u s p1 p2) = (term977 A K k u s p1 p2).
Proof. exact (eq_refl (term1011 A K k u s p1 p2)). Qed.
Lemma lem4475059 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1012 A K k u s p1) = (term979 A K k u s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475058 A K k u s p1 p2)). Qed.
Lemma lem4475060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4475061 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1013 A K k u s p1) = (term980 A K k u s p1).
Proof. exact (MK_COMB (@lem4475060 A) (@lem4475059 A K k u s p1)). Qed.
Lemma lem4475062 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1005 A K k u s p1) = (term998 A K k u s p1).
Proof. exact (MK_COMB (@lem4475057 A K k u p1) (@lem4475061 A K k u s p1)). Qed.
Lemma lem4475063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475064 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1014 A K k u s p1) = (term1015 A K k u s p1).
Proof. exact (MK_COMB (@lem4475063) (@lem4475062 A K k u s p1)). Qed.
Lemma lem4475065 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term1007 A K k u p1 p2) = (term878 A K k u p1 p2).
Proof. exact (eq_refl (term1007 A K k u p1 p2)). Qed.
Lemma lem4475066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4475067 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) : (term1016 A K k u p1 p2) = (term1017 A K k u p1 p2).
Proof. exact (MK_COMB (@lem4475066) (@lem4475065 A K k u p1 p2)). Qed.
Lemma lem4475068 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) : (term1011 A K k u s p1 p2) = (term977 A K k u s p1 p2).
Proof. exact (eq_refl (term1011 A K k u s p1 p2)). Qed.
Lemma lem4475069 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) : (term1018 A K k u s p1 p2) = (term1019 A K k u s p1 p2).
Proof. exact (MK_COMB (@lem4475067 A K k u p1 p2) (@lem4475068 A K k u s p1 p2)). Qed.
Lemma lem4475070 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1020 A K k u s p1) = (term1021 A K k u s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475069 A K k u s p1 p2)). Qed.
Lemma lem4475071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4475072 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1006 A K k u s p1) = (term1022 A K k u s p1).
Proof. exact (MK_COMB (@lem4475071 A) (@lem4475070 A K k u s p1)). Qed.
Lemma lem4475073 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term1005 A K k u s p1) = (term1006 A K k u s p1)) = ((term998 A K k u s p1) = (term1022 A K k u s p1)).
Proof. exact (MK_COMB (@lem4475064 A K k u s p1) (@lem4475072 A K k u s p1)). Qed.
Lemma lem4475074 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term998 A K k u s p1) = (term1022 A K k u s p1).
Proof. exact (EQ_MP (@lem4475073 A K k u s p1) (@lem4475051 A K k u s p1)). Qed.
Lemma lem4475077 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1023 A K k u s p1) = (term1023 A K k u s p1).
Proof. exact (eq_refl (term1023 A K k u s p1)). Qed.
Lemma lem4475078 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1023 A K k u s p1) = ((term998 A K k u s p1) = (term1022 A K k u s p1)).
Proof. exact (eq_refl (term1023 A K k u s p1)). Qed.
Lemma lem4475079 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1024 A K k u s p1) = (term1024 A K k u s p1).
Proof. exact (eq_refl (term1024 A K k u s p1)). Qed.
Lemma lem4475080 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term1023 A K k u s p1) = (term1023 A K k u s p1)) = ((term1023 A K k u s p1) = ((term998 A K k u s p1) = (term1022 A K k u s p1))).
Proof. exact (MK_COMB (@lem4475079 A K k u s p1) (@lem4475078 A K k u s p1)). Qed.
Lemma lem4475081 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1023 A K k u s p1) = ((term998 A K k u s p1) = (term1022 A K k u s p1)).
Proof. exact (eq_refl (term1023 A K k u s p1)). Qed.
Lemma lem4475082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475083 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term1024 A K k u s p1) = (term1025 A K k u s p1).
Proof. exact (MK_COMB (@lem4475082) (@lem4475081 A K k u s p1)). Qed.
Lemma lem4475084 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term998 A K k u s p1) = (term1022 A K k u s p1)) = ((term998 A K k u s p1) = (term1022 A K k u s p1)).
Proof. exact (eq_refl ((term998 A K k u s p1) = (term1022 A K k u s p1))). Qed.
Lemma lem4475085 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term1023 A K k u s p1) = ((term998 A K k u s p1) = (term1022 A K k u s p1))) = (((term998 A K k u s p1) = (term1022 A K k u s p1)) = ((term998 A K k u s p1) = (term1022 A K k u s p1))).
Proof. exact (MK_COMB (@lem4475083 A K k u s p1) (@lem4475084 A K k u s p1)). Qed.
Lemma lem4475086 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term1023 A K k u s p1) = (term1023 A K k u s p1)) = (((term998 A K k u s p1) = (term1022 A K k u s p1)) = ((term998 A K k u s p1) = (term1022 A K k u s p1))).
Proof. exact (TRANS (@lem4475080 A K k u s p1) (@lem4475085 A K k u s p1)). Qed.
Lemma lem4475087 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : ((term998 A K k u s p1) = (term1022 A K k u s p1)) = ((term998 A K k u s p1) = (term1022 A K k u s p1)).
Proof. exact (EQ_MP (@lem4475086 A K k u s p1) (@lem4475077 A K k u s p1)). Qed.
Lemma lem4475088 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term998 A K k u s p1) = (term1022 A K k u s p1).
Proof. exact (EQ_MP (@lem4475087 A K k u s p1) (@lem4475074 A K k u s p1)). Qed.
Lemma lem4475089 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1000 A K k u s) = (term1026 A K k u s).
Proof. exact (fun_ext (fun p1 : K => @lem4475088 A K k u s p1)). Qed.
Lemma lem4475090 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475091 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1001 A K k u s) = (term1027 A K k u s).
Proof. exact (MK_COMB (@lem4475090 K) (@lem4475089 A K k u s)). Qed.
Lemma lem4475092 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term983 A K k u s) = (term1027 A K k u s).
Proof. exact (TRANS (@lem4475047 A K k u s) (@lem4475091 A K k u s)). Qed.
Lemma lem4475093 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term962 A K k u s) = (term1027 A K k u s).
Proof. exact (TRANS (@lem4475006 A K k u s) (@lem4475092 A K k u s)). Qed.
Lemma lem4475094 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term916 A K k u s) = (term1027 A K k u s).
Proof. exact (TRANS (@lem4474922 A K k u s) (@lem4475093 A K k u s)). Qed.
Lemma lem4475095 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term863 A K k u s) = (term1027 A K k u s).
Proof. exact (TRANS (@lem4474580 A K k u s) (@lem4475094 A K k u s)). Qed.
Lemma lem4475096 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term863 A K k u s) : term1027 A K k u s.
Proof. exact (EQ_MP (@lem4475095 A K k u s) (@lem4474423 A K k u s h1)). Qed.
Lemma lem4475097 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (h1 : term1022 A K k u s p1) : term1022 A K k u s p1.
Proof. exact (h1). Qed.
Lemma lem4475121 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) (p2 : A) : (term864 A K u k s p1 p2) = (term864 A K u k s p1 p2).
Proof. exact (eq_refl (term864 A K u k s p1 p2)). Qed.
Lemma lem4475122 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term865 A K u k s p1) = (term865 A K u k s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475121 A K u k s p1 p2)). Qed.
Lemma lem4475123 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4475124 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (p1 : K) : (term866 A K u k s p1) = (term866 A K u k s p1).
Proof. exact (MK_COMB (@lem4475123 A) (@lem4475122 A K u k s p1)). Qed.
Lemma lem4475125 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term867 A K u k s) = (term867 A K u k s).
Proof. exact (fun_ext (fun p1 : K => @lem4475124 A K u k s p1)). Qed.
Lemma lem4475126 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4475127 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term868 A K u k s) = (term868 A K u k s).
Proof. exact (MK_COMB (@lem4475126 K) (@lem4475125 A K u k s)). Qed.
Lemma lem4475128 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term868 A K u k s.
Proof. exact (EQ_MP (@lem4475127 A K u k s) (@lem4474497 A K u k s h1)). Qed.
Lemma lem4475210 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term1019 A K k u s p1 p2) : term1019 A K k u s p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475211 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term878 A K k u p1 p2) : term878 A K k u p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475212 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term977 A K k u s p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475213 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term874 A K k u p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475214 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term871 A K k u p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475215 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term870 A K k u p1 p2.
Proof. exact (proj2 (@lem4475213 A K k u p1 p2 h1)). Qed.
Lemma lem4475219 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term829 A K k u p1 p2.
Proof. exact (proj2 (@lem4475214 A K k u p1 p2 h1)). Qed.
Lemma lem4475223 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term895 A K u s p1 p2.
Proof. exact (proj2 (@lem4475212 A K k u s p1 p2 h1)). Qed.
Lemma lem4475244 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) : (term864 A K u k s p1 p2) = (term1028 A K k u s p1 p2).
Proof. exact (@lem19490 (k p1) (term1029 A K u p1 p2) (s p1 p2)). Qed.
Lemma lem4475245 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term865 A K u k s p1) = (term1030 A K k u s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475244 A K k u s p1 p2)). Qed.
Lemma lem4475246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4475247 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term866 A K u k s p1) = (term1031 A K k u s p1).
Proof. exact (MK_COMB (@lem4475246 A) (@lem4475245 A K k u s p1)). Qed.
Lemma lem4475248 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term867 A K u k s) = (term1032 A K k u s).
Proof. exact (fun_ext (fun p1 : K => @lem4475247 A K k u s p1)). Qed.
Lemma lem4475249 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4475251 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term868 A K u k s) = (term1033 A K k u s).
Proof. exact (MK_COMB (@lem4475249 K) (@lem4475248 A K k u s)). Qed.
Lemma lem4475252 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1033 A K k u s.
Proof. exact (EQ_MP (@lem4475251 A K k u s) (@lem4475128 A K u k s h1)). Qed.
Lemma lem4475260 {K : Type'} (k : K -> Prop) (p1 : K) (h1 : term1034 K k p1) : term1034 K k p1.
Proof. exact (h1). Qed.
Lemma lem4475294 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) : term1029 A K u p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475350 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) : (term864 A K u k s p1 p2) = (term1028 A K k u s p1 p2).
Proof. exact (@lem19490 (k p1) (term1029 A K u p1 p2) (s p1 p2)). Qed.
Lemma lem4475351 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term865 A K u k s p1) = (term1030 A K k u s p1).
Proof. exact (fun_ext (fun p2 : A => @lem4475350 A K k u s p1 p2)). Qed.
Lemma lem4475352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4475353 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) : (term866 A K u k s p1) = (term1031 A K k u s p1).
Proof. exact (MK_COMB (@lem4475352 A) (@lem4475351 A K k u s p1)). Qed.
Lemma lem4475354 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term867 A K u k s) = (term1032 A K k u s).
Proof. exact (fun_ext (fun p1 : K => @lem4475353 A K k u s p1)). Qed.
Lemma lem4475355 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4475357 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term868 A K u k s) = (term1033 A K k u s).
Proof. exact (MK_COMB (@lem4475355 K) (@lem4475354 A K k u s)). Qed.
Lemma lem4475358 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1033 A K k u s.
Proof. exact (EQ_MP (@lem4475357 A K k u s) (@lem4475128 A K u k s h1)). Qed.
Lemma lem4475371 {A K : Type'} (_51729 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1035 A K k u s _51729.
Proof. exact (@lem4475252 A K u k s h1 _51729). Qed.
Lemma lem4475372 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (_51729 : K) : (term1035 A K k u s _51729) = (term1031 A K k u s _51729).
Proof. exact (eq_refl (term1035 A K k u s _51729)). Qed.
Lemma lem4475373 {A K : Type'} (_51729 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1031 A K k u s _51729.
Proof. exact (EQ_MP (@lem4475372 A K k u s _51729) (@lem4475371 A K _51729 u k s h1)). Qed.
Lemma lem4475374 {A K : Type'} (_51729 : K) (_51730 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1036 A K k u s _51729 _51730.
Proof. exact (@lem4475373 A K _51729 u k s h1 _51730). Qed.
Lemma lem4475375 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (_51729 : K) (_51730 : A) : (term1036 A K k u s _51729 _51730) = (term1028 A K k u s _51729 _51730).
Proof. exact (eq_refl (term1036 A K k u s _51729 _51730)). Qed.
Lemma lem4475376 {A K : Type'} (_51729 : K) (_51730 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1028 A K k u s _51729 _51730.
Proof. exact (EQ_MP (@lem4475375 A K k u s _51729 _51730) (@lem4475374 A K _51729 _51730 u k s h1)). Qed.
Lemma lem4475389 {A K : Type'} (_51735 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1035 A K k u s _51735.
Proof. exact (@lem4475358 A K u k s h1 _51735). Qed.
Lemma lem4475390 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (_51735 : K) : (term1035 A K k u s _51735) = (term1031 A K k u s _51735).
Proof. exact (eq_refl (term1035 A K k u s _51735)). Qed.
Lemma lem4475391 {A K : Type'} (_51735 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1031 A K k u s _51735.
Proof. exact (EQ_MP (@lem4475390 A K k u s _51735) (@lem4475389 A K _51735 u k s h1)). Qed.
Lemma lem4475392 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1036 A K k u s _51735 _51736.
Proof. exact (@lem4475391 A K _51735 u k s h1 _51736). Qed.
Lemma lem4475393 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (_51735 : K) (_51736 : A) : (term1036 A K k u s _51735 _51736) = (term1028 A K k u s _51735 _51736).
Proof. exact (eq_refl (term1036 A K k u s _51735 _51736)). Qed.
Lemma lem4475394 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1028 A K k u s _51735 _51736.
Proof. exact (EQ_MP (@lem4475393 A K k u s _51735 _51736) (@lem4475392 A K _51735 _51736 u k s h1)). Qed.
Lemma lem4475406 {K : Type'} (k : K -> Prop) (p1 : K) (h1 : term1034 K k p1) : term1034 K k p1.
Proof. exact (h1). Qed.
Lemma lem4475412 {A K : Type'} (_51730 : A) (_51729 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1037 A K u _51730 k _51729.
Proof. exact (proj1 (@lem4475376 A K _51729 _51730 u k s h1)). Qed.
Lemma lem4475422 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) : term1029 A K u p1 p2.
Proof. exact (h1). Qed.
Lemma lem4475436 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term1029 A K u p1 p2.
Proof. exact (proj1 (@lem4475214 A K k u p1 p2 h1)). Qed.
Lemma lem4475458 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term1038 A K s p1 p2.
Proof. exact (proj2 (@lem4475223 A K k u s p1 p2 h1)). Qed.
Lemma lem4475470 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1039 A K u s _51735 _51736.
Proof. exact (proj2 (@lem4475394 A K _51735 _51736 u k s h1)). Qed.
Lemma lem4475472 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (proj1 (@lem4475213 A K k u p1 p2 h1)). Qed.
Lemma lem4475473 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term1040 A K u p1 p2.
Proof. exact (fun h0 : term1029 A K u p1 p2 => @lem4475472 A K k u p1 p2 h1). Qed.
Lemma lem4475475 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475476 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1040 A K u p1 p2) = (term801 A K u p1 p2).
Proof. exact (@lem4475475 (term801 A K u p1 p2)). Qed.
Lemma lem4475477 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475476 A K u p1 p2) (@lem4475473 A K k u p1 p2 h1)). Qed.
Lemma lem4475483 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4475484 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1037 A K u _51730 k _51729) = (term1041 A K k u _51729 _51730).
Proof. exact (@lem4475483 (k _51729) (term1029 A K u _51729 _51730)). Qed.
Lemma lem4475490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475491 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1042 A K u _51730 k _51729) = (term1043 A K k u _51729 _51730).
Proof. exact (MK_COMB (@lem4475490) (@lem4475484 A K k u _51729 _51730)). Qed.
Lemma lem4475497 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1041 A K k u _51729 _51730) = (term1041 A K k u _51729 _51730).
Proof. exact (eq_refl (term1041 A K k u _51729 _51730)). Qed.
Lemma lem4475498 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : ((term1037 A K u _51730 k _51729) = (term1041 A K k u _51729 _51730)) = ((term1041 A K k u _51729 _51730) = (term1041 A K k u _51729 _51730)).
Proof. exact (MK_COMB (@lem4475491 A K k u _51729 _51730) (@lem4475497 A K k u _51729 _51730)). Qed.
Lemma lem4475500 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4475501 (x : Prop) : (x = x) = True.
Proof. exact (@lem4475500 Prop x). Qed.
Lemma lem4475502 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : ((term1041 A K k u _51729 _51730) = (term1041 A K k u _51729 _51730)) = True.
Proof. exact (@lem4475501 (term1041 A K k u _51729 _51730)). Qed.
Lemma lem4475503 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : ((term1037 A K u _51730 k _51729) = (term1041 A K k u _51729 _51730)) = True.
Proof. exact (TRANS (@lem4475498 A K k u _51729 _51730) (@lem4475502 A K k u _51729 _51730)). Qed.
Lemma lem4475504 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : True = ((term1037 A K u _51730 k _51729) = (term1041 A K k u _51729 _51730)).
Proof. exact (SYM (@lem4475503 A K k u _51729 _51730)). Qed.
Lemma lem4475505 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1037 A K u _51730 k _51729) = (term1041 A K k u _51729 _51730).
Proof. exact (EQ_MP (@lem4475504 A K k u _51729 _51730) (@lem0)). Qed.
Lemma lem4475506 {A K : Type'} (_51729 : K) (_51730 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1041 A K k u _51729 _51730.
Proof. exact (EQ_MP (@lem4475505 A K k u _51729 _51730) (@lem4475412 A K _51730 _51729 u k s h1)). Qed.
Lemma lem4475508 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4475509 {A K : Type'} (u : type1223 A K) (_51730 : A) (k : K -> Prop) (_51729 : K) : (term1041 A K k u _51729 _51730) = (term1044 A K u _51730 k _51729).
Proof. exact (@lem4475508 (term1029 A K u _51729 _51730) (k _51729)). Qed.
Lemma lem4475511 (a : Prop) : (term629 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4475512 {A K : Type'} (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1045 A K u _51729 _51730) = (term801 A K u _51729 _51730).
Proof. exact (@lem4475511 (term801 A K u _51729 _51730)). Qed.
Lemma lem4475513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4475514 {A K : Type'} (u : type1223 A K) (_51729 : K) (_51730 : A) : (term1046 A K u _51729 _51730) = (term802 A K u _51729 _51730).
Proof. exact (MK_COMB (@lem4475513) (@lem4475512 A K u _51729 _51730)). Qed.
Lemma lem4475515 {K : Type'} (k : K -> Prop) (_51729 : K) : (k _51729) = (k _51729).
Proof. exact (eq_refl (k _51729)). Qed.
Lemma lem4475516 {A K : Type'} (u : type1223 A K) (_51730 : A) (k : K -> Prop) (_51729 : K) : (term1044 A K u _51730 k _51729) = (term1047 A K u _51730 k _51729).
Proof. exact (MK_COMB (@lem4475514 A K u _51729 _51730) (@lem4475515 K k _51729)). Qed.
Lemma lem4475517 {A K : Type'} (u : type1223 A K) (_51730 : A) (k : K -> Prop) (_51729 : K) : (term1041 A K k u _51729 _51730) = (term1047 A K u _51730 k _51729).
Proof. exact (TRANS (@lem4475509 A K u _51730 k _51729) (@lem4475516 A K u _51730 k _51729)). Qed.
Lemma lem4475520 {A K : Type'} (_51730 : A) (_51729 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1047 A K u _51730 k _51729.
Proof. exact (EQ_MP (@lem4475517 A K u _51730 k _51729) (@lem4475506 A K _51729 _51730 u k s h1)). Qed.
Lemma lem4475521 {A K : Type'} (_51730 : A) (_51729 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1047 A K u _51730 k _51729.
Proof. exact (@lem4475520 A K _51730 _51729 u k s h1). Qed.
Lemma lem4475522 {A K : Type'} (p2 : A) (p1 : K) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1047 A K u p2 k p1.
Proof. exact (@lem4475521 A K p2 p1 u k s h1). Qed.
Lemma lem4475525 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term874 A K k u p1 p2) : k p1.
Proof. exact (@lem4475522 A K p2 p1 u k s h1 (@lem4475477 A K k u p1 p2 h2)). Qed.
Lemma lem4475526 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term874 A K k u p1 p2) : term1048 K k p1.
Proof. exact (fun h0 : term1034 K k p1 => @lem4475525 A K s k u p1 p2 h1 h2). Qed.
Lemma lem4475528 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475529 {K : Type'} (k : K -> Prop) (p1 : K) : (term1048 K k p1) = (k p1).
Proof. exact (@lem4475528 (k p1)). Qed.
Lemma lem4475530 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term874 A K k u p1 p2) : k p1.
Proof. exact (EQ_MP (@lem4475529 K k p1) (@lem4475526 A K s k u p1 p2 h1 h2)). Qed.
Lemma lem4475533 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4475535 {K : Type'} (k : K -> Prop) (p1 : K) : (term1034 K k p1) = (term1049 K k p1).
Proof. exact (@lem4475533 (k p1)). Qed.
Lemma lem4475538 {K : Type'} (k : K -> Prop) (p1 : K) (h1 : term1034 K k p1) : term1049 K k p1.
Proof. exact (EQ_MP (@lem4475535 K k p1) (@lem4475406 K k p1 h1)). Qed.
Lemma lem4475541 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : False.
Proof. exact (@lem4475538 K k p1 h2 (@lem4475530 A K s k u p1 p2 h1 h3)). Qed.
Lemma lem4475542 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : term643.
Proof. exact (fun h0 : ~ False => @lem4475541 A K s k u p1 p2 h1 h2 h3). Qed.
Lemma lem4475544 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475545 : term643 = False.
Proof. exact (@lem4475544 False). Qed.
Lemma lem4475546 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475545) (@lem4475542 A K s k u p1 p2 h1 h2 h3)). Qed.
Lemma lem4475548 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (proj1 (@lem4475213 A K k u p1 p2 h1)). Qed.
Lemma lem4475549 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term1040 A K u p1 p2.
Proof. exact (fun h0 : term1029 A K u p1 p2 => @lem4475548 A K k u p1 p2 h1). Qed.
Lemma lem4475551 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475552 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1040 A K u p1 p2) = (term801 A K u p1 p2).
Proof. exact (@lem4475551 (term801 A K u p1 p2)). Qed.
Lemma lem4475553 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term874 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475552 A K u p1 p2) (@lem4475549 A K k u p1 p2 h1)). Qed.
Lemma lem4475556 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4475558 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1029 A K u p1 p2) = (term1050 A K u p1 p2).
Proof. exact (@lem4475556 (term801 A K u p1 p2)). Qed.
Lemma lem4475561 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) : term1050 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475558 A K u p1 p2) (@lem4475422 A K u p1 p2 h1)). Qed.
Lemma lem4475564 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (@lem4475561 A K u p1 p2 h1 (@lem4475553 A K k u p1 p2 h2)). Qed.
Lemma lem4475565 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : term643.
Proof. exact (fun h0 : ~ False => @lem4475564 A K k u p1 p2 h1 h2). Qed.
Lemma lem4475567 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475568 : term643 = False.
Proof. exact (@lem4475567 False). Qed.
Lemma lem4475569 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475568) (@lem4475565 A K k u p1 p2 h1 h2)). Qed.
Lemma lem4475571 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (proj2 (@lem4475219 A K k u p1 p2 h1)). Qed.
Lemma lem4475572 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term1040 A K u p1 p2.
Proof. exact (fun h0 : term1029 A K u p1 p2 => @lem4475571 A K k u p1 p2 h1). Qed.
Lemma lem4475574 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475575 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1040 A K u p1 p2) = (term801 A K u p1 p2).
Proof. exact (@lem4475574 (term801 A K u p1 p2)). Qed.
Lemma lem4475576 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term801 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475575 A K u p1 p2) (@lem4475572 A K k u p1 p2 h1)). Qed.
Lemma lem4475579 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4475581 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1029 A K u p1 p2) = (term1050 A K u p1 p2).
Proof. exact (@lem4475579 (term801 A K u p1 p2)). Qed.
Lemma lem4475584 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term1050 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475581 A K u p1 p2) (@lem4475436 A K k u p1 p2 h1)). Qed.
Lemma lem4475587 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : False.
Proof. exact (@lem4475584 A K k u p1 p2 h1 (@lem4475576 A K k u p1 p2 h1)). Qed.
Lemma lem4475588 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : term643.
Proof. exact (fun h0 : ~ False => @lem4475587 A K k u p1 p2 h1). Qed.
Lemma lem4475590 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475591 : term643 = False.
Proof. exact (@lem4475590 False). Qed.
Lemma lem4475592 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term871 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475591) (@lem4475588 A K k u p1 p2 h1)). Qed.
Lemma lem4475594 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term801 A K u p1 p2.
Proof. exact (proj1 (@lem4475223 A K k u s p1 p2 h1)). Qed.
Lemma lem4475595 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term1040 A K u p1 p2.
Proof. exact (fun h0 : term1029 A K u p1 p2 => @lem4475594 A K k u s p1 p2 h1). Qed.
Lemma lem4475597 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475598 {A K : Type'} (u : type1223 A K) (p1 : K) (p2 : A) : (term1040 A K u p1 p2) = (term801 A K u p1 p2).
Proof. exact (@lem4475597 (term801 A K u p1 p2)). Qed.
Lemma lem4475599 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term801 A K u p1 p2.
Proof. exact (EQ_MP (@lem4475598 A K u p1 p2) (@lem4475595 A K k u s p1 p2 h1)). Qed.
Lemma lem4475605 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4475606 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1039 A K u s _51735 _51736) = (term1051 A K s u _51735 _51736).
Proof. exact (@lem4475605 (s _51735 _51736) (term1029 A K u _51735 _51736)). Qed.
Lemma lem4475612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475613 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1052 A K u s _51735 _51736) = (term1053 A K s u _51735 _51736).
Proof. exact (MK_COMB (@lem4475612) (@lem4475606 A K s u _51735 _51736)). Qed.
Lemma lem4475619 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1051 A K s u _51735 _51736) = (term1051 A K s u _51735 _51736).
Proof. exact (eq_refl (term1051 A K s u _51735 _51736)). Qed.
Lemma lem4475620 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : ((term1039 A K u s _51735 _51736) = (term1051 A K s u _51735 _51736)) = ((term1051 A K s u _51735 _51736) = (term1051 A K s u _51735 _51736)).
Proof. exact (MK_COMB (@lem4475613 A K s u _51735 _51736) (@lem4475619 A K s u _51735 _51736)). Qed.
Lemma lem4475622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4475623 (x : Prop) : (x = x) = True.
Proof. exact (@lem4475622 Prop x). Qed.
Lemma lem4475624 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : ((term1051 A K s u _51735 _51736) = (term1051 A K s u _51735 _51736)) = True.
Proof. exact (@lem4475623 (term1051 A K s u _51735 _51736)). Qed.
Lemma lem4475625 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : ((term1039 A K u s _51735 _51736) = (term1051 A K s u _51735 _51736)) = True.
Proof. exact (TRANS (@lem4475620 A K s u _51735 _51736) (@lem4475624 A K s u _51735 _51736)). Qed.
Lemma lem4475626 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : True = ((term1039 A K u s _51735 _51736) = (term1051 A K s u _51735 _51736)).
Proof. exact (SYM (@lem4475625 A K s u _51735 _51736)). Qed.
Lemma lem4475627 {A K : Type'} (s : type1470 A K) (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1039 A K u s _51735 _51736) = (term1051 A K s u _51735 _51736).
Proof. exact (EQ_MP (@lem4475626 A K s u _51735 _51736) (@lem0)). Qed.
Lemma lem4475628 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term1051 A K s u _51735 _51736.
Proof. exact (EQ_MP (@lem4475627 A K s u _51735 _51736) (@lem4475470 A K _51735 _51736 u k s h1)). Qed.
Lemma lem4475630 (b : Prop) (a : Prop) : (a \/ b) = (term620 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4475631 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (_51735 : K) (_51736 : A) : (term1051 A K s u _51735 _51736) = (term1054 A K u s _51735 _51736).
Proof. exact (@lem4475630 (term1029 A K u _51735 _51736) (s _51735 _51736)). Qed.
Lemma lem4475633 (a : Prop) : (term629 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4475634 {A K : Type'} (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1045 A K u _51735 _51736) = (term801 A K u _51735 _51736).
Proof. exact (@lem4475633 (term801 A K u _51735 _51736)). Qed.
Lemma lem4475635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4475636 {A K : Type'} (u : type1223 A K) (_51735 : K) (_51736 : A) : (term1046 A K u _51735 _51736) = (term802 A K u _51735 _51736).
Proof. exact (MK_COMB (@lem4475635) (@lem4475634 A K u _51735 _51736)). Qed.
Lemma lem4475637 {A K : Type'} (s : type1470 A K) (_51735 : K) (_51736 : A) : (s _51735 _51736) = (s _51735 _51736).
Proof. exact (eq_refl (s _51735 _51736)). Qed.
Lemma lem4475638 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (_51735 : K) (_51736 : A) : (term1054 A K u s _51735 _51736) = (term836 A K u s _51735 _51736).
Proof. exact (MK_COMB (@lem4475636 A K u _51735 _51736) (@lem4475637 A K s _51735 _51736)). Qed.
Lemma lem4475639 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (_51735 : K) (_51736 : A) : (term1051 A K s u _51735 _51736) = (term836 A K u s _51735 _51736).
Proof. exact (TRANS (@lem4475631 A K u s _51735 _51736) (@lem4475638 A K u s _51735 _51736)). Qed.
Lemma lem4475642 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term836 A K u s _51735 _51736.
Proof. exact (EQ_MP (@lem4475639 A K u s _51735 _51736) (@lem4475628 A K _51735 _51736 u k s h1)). Qed.
Lemma lem4475643 {A K : Type'} (_51735 : K) (_51736 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term836 A K u s _51735 _51736.
Proof. exact (@lem4475642 A K _51735 _51736 u k s h1). Qed.
Lemma lem4475644 {A K : Type'} (p1 : K) (p2 : A) (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term836 A K u s p1 p2.
Proof. exact (@lem4475643 A K p1 p2 u k s h1). Qed.
Lemma lem4475647 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : s p1 p2.
Proof. exact (@lem4475644 A K p1 p2 u k s h1 (@lem4475599 A K k u s p1 p2 h2)). Qed.
Lemma lem4475648 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : term1055 A K s p1 p2.
Proof. exact (fun h0 : term1038 A K s p1 p2 => @lem4475647 A K k u s p1 p2 h1 h2). Qed.
Lemma lem4475650 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475651 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term1055 A K s p1 p2) = (s p1 p2).
Proof. exact (@lem4475650 (s p1 p2)). Qed.
Lemma lem4475652 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : s p1 p2.
Proof. exact (EQ_MP (@lem4475651 A K s p1 p2) (@lem4475648 A K k u s p1 p2 h1 h2)). Qed.
Lemma lem4475655 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4475657 {A K : Type'} (s : type1470 A K) (p1 : K) (p2 : A) : (term1038 A K s p1 p2) = (term1056 A K s p1 p2).
Proof. exact (@lem4475655 (s p1 p2)). Qed.
Lemma lem4475660 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term977 A K k u s p1 p2) : term1056 A K s p1 p2.
Proof. exact (EQ_MP (@lem4475657 A K s p1 p2) (@lem4475458 A K k u s p1 p2 h1)). Qed.
Lemma lem4475663 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : False.
Proof. exact (@lem4475660 A K k u s p1 p2 h2 (@lem4475652 A K k u s p1 p2 h1 h2)). Qed.
Lemma lem4475664 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : term643.
Proof. exact (fun h0 : ~ False => @lem4475663 A K k u s p1 p2 h1 h2). Qed.
Lemma lem4475666 (p : Prop) : (term624 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4475667 : term643 = False.
Proof. exact (@lem4475666 False). Qed.
Lemma lem4475668 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term977 A K k u s p1 p2) : False.
Proof. exact (EQ_MP (@lem4475667) (@lem4475664 A K k u s p1 p2 h1 h2)). Qed.
Lemma lem4475669 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : (term1029 A K u p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term1029 A K u p1 p2 => @lem4475569 A K k u p1 p2 h1 h2) (fun h3 : False => @lem4475422 A K u p1 p2 h1)). Qed.
Lemma lem4475670 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475669 A K k u p1 p2 h1 h2) (@lem4475422 A K u p1 p2 h1)). Qed.
Lemma lem4475671 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : (term1034 K k p1) = False.
Proof. exact (prop_ext (fun h4 : term1034 K k p1 => @lem4475546 A K s k u p1 p2 h1 h2 h3) (fun h4 : False => @lem4475406 K k p1 h2)). Qed.
Lemma lem4475672 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475671 A K s k u p1 p2 h1 h2 h3) (@lem4475406 K k p1 h2)). Qed.
Lemma lem4475673 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : (term1029 A K u p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term1029 A K u p1 p2 => @lem4475670 A K k u p1 p2 h1 h2) (fun h3 : False => @lem4475294 A K u p1 p2 h1)). Qed.
Lemma lem4475674 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475673 A K k u p1 p2 h1 h2) (@lem4475294 A K u p1 p2 h1)). Qed.
Lemma lem4475675 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : (term1034 K k p1) = False.
Proof. exact (prop_ext (fun h4 : term1034 K k p1 => @lem4475672 A K s k u p1 p2 h1 h2 h3) (fun h4 : False => @lem4475260 K k p1 h2)). Qed.
Lemma lem4475676 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475675 A K s k u p1 p2 h1 h2 h3) (@lem4475260 K k p1 h2)). Qed.
Lemma lem4475677 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : (term1029 A K u p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term1029 A K u p1 p2 => @lem4475674 A K k u p1 p2 h1 h2) (fun h3 : False => @lem4475294 A K u p1 p2 h1)). Qed.
Lemma lem4475678 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term1029 A K u p1 p2) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475677 A K k u p1 p2 h1 h2) (@lem4475294 A K u p1 p2 h1)). Qed.
Lemma lem4475679 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : (term1034 K k p1) = False.
Proof. exact (prop_ext (fun h4 : term1034 K k p1 => @lem4475676 A K s k u p1 p2 h1 h2 h3) (fun h4 : False => @lem4475260 K k p1 h2)). Qed.
Lemma lem4475680 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1034 K k p1) (h3 : term874 A K k u p1 p2) : False.
Proof. exact (EQ_MP (@lem4475679 A K s k u p1 p2 h1 h2 h3) (@lem4475260 K k p1 h2)). Qed.
Lemma lem4475681 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term874 A K k u p1 p2) : False.
Proof. exact (or_elim (@lem4475215 A K k u p1 p2 h2) (fun h0 : term1034 K k p1 => @lem4475680 A K s k u p1 p2 h1 h0 h2) (fun h0 : term1029 A K u p1 p2 => @lem4475678 A K k u p1 p2 h0 h2)). Qed.
Lemma lem4475682 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (u : type1223 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term878 A K k u p1 p2) : False.
Proof. exact (or_elim (@lem4475211 A K k u p1 p2 h2) (fun h0 : term874 A K k u p1 p2 => @lem4475681 A K s k u p1 p2 h1 h0) (fun h0 : term871 A K k u p1 p2 => @lem4475592 A K k u p1 p2 h0)). Qed.
Lemma lem4475683 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1019 A K k u s p1 p2) : False.
Proof. exact (or_elim (@lem4475210 A K k u s p1 p2 h2) (fun h0 : term878 A K k u p1 p2 => @lem4475682 A K s k u p1 p2 h1 h0) (fun h0 : term977 A K k u s p1 p2 => @lem4475668 A K k u s p1 p2 h1 h0)). Qed.
Lemma lem4475684 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1019 A K k u s p1 p2) : (term1019 A K k u s p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term1019 A K k u s p1 p2 => @lem4475683 A K k u s p1 p2 h1 h2) (fun h3 : False => @lem4475210 A K k u s p1 p2 h2)). Qed.
Lemma lem4475685 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (p2 : A) (h1 : term809 A K u k s) (h2 : term1019 A K k u s p1 p2) : False.
Proof. exact (EQ_MP (@lem4475684 A K k u s p1 p2 h1 h2) (@lem4475210 A K k u s p1 p2 h2)). Qed.
Lemma lem4475686 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (p1 : K) (h1 : term809 A K u k s) (h2 : term1022 A K k u s p1) : False.
Proof. exact (ex_elim (@lem4475097 A K k u s p1 h2) (fun p2 : A => fun h0 : term1021 A K k u s p1 p2 => @lem4475685 A K k u s p1 p2 h1 h0)). Qed.
Lemma lem4475687 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term809 A K u k s) (h2 : term863 A K k u s) : False.
Proof. exact (ex_elim (@lem4475096 A K k u s h2) (fun p1 : K => fun h0 : term1026 A K k u s p1 => @lem4475686 A K k u s p1 h1 h0)). Qed.
Lemma lem4475688 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term809 A K u k s) (h2 : term863 A K k u s) : (term863 A K k u s) = False.
Proof. exact (prop_ext (fun h3 : term863 A K k u s => @lem4475687 A K k u s h1 h2) (fun h3 : False => @lem4474423 A K k u s h2)). Qed.
Lemma lem4475689 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term809 A K u k s) (h2 : term863 A K k u s) : False.
Proof. exact (EQ_MP (@lem4475688 A K k u s h1 h2) (@lem4474423 A K k u s h2)). Qed.
Lemma lem4475690 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term862 A K k u s.
Proof. exact (fun h0 : term863 A K k u s => @lem4475689 A K k u s h1 h0). Qed.
Lemma lem4475691 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term809 A K u k s) : term842 A K k u s.
Proof. exact (EQ_MP (@lem4474422 A K k u s) (@lem4475690 A K u k s h1)). Qed.
Lemma lem4475692 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term843 A K k u s.
Proof. exact (fun h0 : term809 A K u k s => @lem4475691 A K u k s h0). Qed.
Lemma lem4475697 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : term853 A K u s.
Proof. exact (fun k : K -> Prop => @lem4475692 A K k u s). Qed.
Lemma lem4475702 {A K : Type'} (s : type1470 A K) : term857 A K s.
Proof. exact (fun u : type1223 A K => @lem4475697 A K u s). Qed.
Lemma lem4475707 {A K : Type'} : term861 A K.
Proof. exact (fun s : type1470 A K => @lem4475702 A K s). Qed.
Lemma lem4475708 {A K : Type'} : term860 A K.
Proof. exact (EQ_MP (@lem4474417 A K) (@lem4475707 A K)). Qed.
Lemma lem4475709 {A K : Type'} (s : type1470 A K) : term1057 A K s.
Proof. exact (@lem4475708 A K s). Qed.
Lemma lem4475710 {A K : Type'} (s : type1470 A K) : (term1057 A K s) = (term856 A K s).
Proof. exact (eq_refl (term1057 A K s)). Qed.
Lemma lem4475711 {A K : Type'} (s : type1470 A K) : term856 A K s.
Proof. exact (EQ_MP (@lem4475710 A K s) (@lem4475709 A K s)). Qed.
Lemma lem4475712 {A K : Type'} (s : type1470 A K) (u : type1223 A K) : term1058 A K s u.
Proof. exact (@lem4475711 A K s u). Qed.
Lemma lem4475713 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : (term1058 A K s u) = (term852 A K u s).
Proof. exact (eq_refl (term1058 A K s u)). Qed.
Lemma lem4475714 {A K : Type'} (u : type1223 A K) (s : type1470 A K) : term852 A K u s.
Proof. exact (EQ_MP (@lem4475713 A K u s) (@lem4475712 A K s u)). Qed.
Lemma lem4475715 {A K : Type'} (u : type1223 A K) (s : type1470 A K) (k : K -> Prop) : term1059 A K u s k.
Proof. exact (@lem4475714 A K u s k). Qed.
Lemma lem4475716 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : (term1059 A K u s k) = (term844 A K k u s).
Proof. exact (eq_refl (term1059 A K u s k)). Qed.
Lemma lem4475717 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term844 A K k u s.
Proof. exact (EQ_MP (@lem4475716 A K k u s) (@lem4475715 A K u s k)). Qed.
Lemma lem4475719 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term844 A K k u s.
Proof. exact (@lem4474203 A K k u s (@lem4475717 A K k u s)). Qed.
Lemma lem4475720 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term845 A K k u s) : False.
Proof. exact (@lem4475719 A K k u s (@lem4474187 A K k u s h1)). Qed.
Lemma lem4475721 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term845 A K k u s) : (term845 A K k u s) = False.
Proof. exact (prop_ext (fun h2 : term845 A K k u s => @lem4475720 A K k u s h1) (fun h2 : False => @lem4474187 A K k u s h1)). Qed.
Lemma lem4475722 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) (h1 : term845 A K k u s) : False.
Proof. exact (EQ_MP (@lem4475721 A K k u s h1) (@lem4474187 A K k u s h1)). Qed.
Lemma lem4475723 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term844 A K k u s.
Proof. exact (fun h0 : term845 A K k u s => @lem4475722 A K k u s h0). Qed.
Lemma lem4475724 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term843 A K k u s.
Proof. exact (EQ_MP (@lem4474186 A K k u s) (@lem4475723 A K k u s)). Qed.
Lemma lem4475726 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term800 A K k u s.
Proof. exact (EQ_MP (@lem4474182 A K k u s) (@lem4475724 A K k u s)). Qed.
Lemma lem4475727 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term687 A K k u s.
Proof. exact (EQ_MP (@lem4473925 A K k u s) (@lem4475726 A K k u s)). Qed.
Lemma lem4475728 {A K : Type'} (k : K -> Prop) (u : type1223 A K) (s : type1470 A K) : term686 A K k u s.
Proof. exact (EQ_MP (@lem4473617 A K k u s) (@lem4475727 A K k u s)). Qed.
Lemma lem4475729 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term21 A K u k s) : term684 A K k u s.
Proof. exact (@lem4475728 A K k u s (@lem4469852 A K u k s h1)). Qed.
Lemma lem4475730 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term21 A K u k s) : term74 A K u k s.
Proof. exact (ex_intro (term73 A K u k s) (term662 A K u) (@lem4475729 A K u k s h1)). Qed.
Lemma lem4475731 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term1060 A K u k s.
Proof. exact (fun h0 : term21 A K u k s => @lem4475730 A K u k s h0). Qed.
Lemma lem4475732 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : term1061 A K u k s.
Proof. exact (conj (@lem4475731 A K u k s) (@lem4473514 A K u k s)). Qed.
Lemma lem4475733 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term1061 A K u k s) = ((term21 A K u k s) = (term74 A K u k s)).
Proof. exact (@lem32 (term21 A K u k s) (term74 A K u k s)). Qed.
Lemma lem4475734 {A K : Type'} (u : type1223 A K) (k : K -> Prop) (s : type1470 A K) : (term21 A K u k s) = (term74 A K u k s).
Proof. exact (EQ_MP (@lem4475733 A K u k s) (@lem4475732 A K u k s)). Qed.
Lemma lem4475739 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term1062 A K k s.
Proof. exact (fun u : type1223 A K => @lem4475734 A K u k s). Qed.
Lemma lem4475744 {A K : Type'} (k : K -> Prop) : term1063 A K k.
Proof. exact (fun s : type1470 A K => @lem4475739 A K k s). Qed.
Lemma lem4475749 {A K : Type'} : term1064 A K.
Proof. exact (fun k : K -> Prop => @lem4475744 A K k). Qed.
