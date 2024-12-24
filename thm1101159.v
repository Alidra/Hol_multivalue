Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1101159_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1100896 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1100897 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1100898 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1100897 A B f) (@lem1100896 A B f)). Qed.
Lemma lem1100899 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1100898 A B f y). Qed.
Lemma lem1100900 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1100903 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : EX' = (term4 _25328 _17976).
Proof. exact (h1). Qed.
Lemma lem1100904 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100905 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100903 _25328 EX' _17976 h1) (@lem1100904 _25328 P)). Qed.
Lemma lem1100907 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1100908 {_25328 : Type'} (f : type663 _25328) (y : _25328 -> Prop) : (term6 _25328 f y) = (f y).
Proof. exact (@lem1100907 (_25328 -> Prop) (type1143 _25328) f y). Qed.
Lemma lem1100909 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (@lem1100908 _25328 (term4 _25328 _17976) P). Qed.
Lemma lem1100910 {_25328 : Type'} (_17976 : type1131 _25328) (_17974 : _25328 -> Prop) : (term5 _25328 _17976 _17974) = (term8 _25328 _17976 _17974).
Proof. exact (eq_refl (term5 _25328 _17976 _17974)). Qed.
Lemma lem1100911 {_25328 : Type'} (_17976 : type1131 _25328) : (term9 _25328 _17976) = (term4 _25328 _17976).
Proof. exact (fun_ext (fun _17974 : _25328 -> Prop => @lem1100910 _25328 _17976 _17974)). Qed.
Lemma lem1100912 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100913 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100911 _25328 _17976) (@lem1100912 _25328 P)). Qed.
Lemma lem1100914 {_25328 : Type'} : (@eq ((list _25328) -> Prop)) = (@eq ((list _25328) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25328) -> Prop))). Qed.
Lemma lem1100915 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term10 _25328 _17976 P) = (term11 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100914 _25328) (@lem1100913 _25328 _17976 P)). Qed.
Lemma lem1100916 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (eq_refl (term5 _25328 _17976 P)). Qed.
Lemma lem1100917 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : ((term7 _25328 _17976 P) = (term5 _25328 _17976 P)) = ((term5 _25328 _17976 P) = (term8 _25328 _17976 P)).
Proof. exact (MK_COMB (@lem1100915 _25328 _17976 P) (@lem1100916 _25328 _17976 P)). Qed.
Lemma lem1100918 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (EQ_MP (@lem1100917 _25328 _17976 P) (@lem1100909 _25328 _17976 P)). Qed.
Lemma lem1100919 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term8 _25328 _17976 P).
Proof. exact (TRANS (@lem1100905 _25328 P EX' _17976 h1) (@lem1100918 _25328 _17976 P)). Qed.
Lemma lem1100920 {_25328 : Type'} : (@nil _25328) = (@nil _25328).
Proof. exact (eq_refl (@nil _25328)). Qed.
Lemma lem1100921 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P (@nil _25328)) = (term12 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100919 _25328 P EX' _17976 h1) (@lem1100920 _25328)). Qed.
Lemma lem1100923 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1100924 {_25328 : Type'} (f : type1143 _25328) (y : list _25328) : (term13 _25328 f y) = (f y).
Proof. exact (@lem1100923 (list _25328) Prop f y). Qed.
Lemma lem1100925 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term14 _25328 _17976 P) = (term12 _25328 _17976 P).
Proof. exact (@lem1100924 _25328 (term8 _25328 _17976 P) (@nil _25328)). Qed.
Lemma lem1100926 {_25328 : Type'} (_17976 : type1131 _25328) (_17975 : list _25328) (P : _25328 -> Prop) : (term15 _25328 _17976 P _17975) = (_17976 _17975 P).
Proof. exact (eq_refl (term15 _25328 _17976 P _17975)). Qed.
Lemma lem1100927 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term16 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (fun_ext (fun _17975 : list _25328 => @lem1100926 _25328 _17976 _17975 P)). Qed.
Lemma lem1100928 {_25328 : Type'} : (@nil _25328) = (@nil _25328).
Proof. exact (eq_refl (@nil _25328)). Qed.
Lemma lem1100929 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term14 _25328 _17976 P) = (term12 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100927 _25328 _17976 P) (@lem1100928 _25328)). Qed.
Lemma lem1100930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100931 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term17 _25328 _17976 P) = (term18 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100930) (@lem1100929 _25328 _17976 P)). Qed.
Lemma lem1100932 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term12 _25328 _17976 P) = (_17976 (@nil _25328) P).
Proof. exact (eq_refl (term12 _25328 _17976 P)). Qed.
Lemma lem1100933 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : ((term14 _25328 _17976 P) = (term12 _25328 _17976 P)) = ((term12 _25328 _17976 P) = (_17976 (@nil _25328) P)).
Proof. exact (MK_COMB (@lem1100931 _25328 _17976 P) (@lem1100932 _25328 _17976 P)). Qed.
Lemma lem1100934 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term12 _25328 _17976 P) = (_17976 (@nil _25328) P).
Proof. exact (EQ_MP (@lem1100933 _25328 _17976 P) (@lem1100925 _25328 _17976 P)). Qed.
Lemma lem1100935 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P (@nil _25328)) = (_17976 (@nil _25328) P).
Proof. exact (TRANS (@lem1100921 _25328 P EX' _17976 h1) (@lem1100934 _25328 _17976 P)). Qed.
Lemma lem1100936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100937 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term19 _25328 EX' P) = (term20 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100936) (@lem1100935 _25328 P EX' _17976 h1)). Qed.
Lemma lem1100938 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1100939 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : ((EX' P (@nil _25328)) = False) = ((_17976 (@nil _25328) P) = False).
Proof. exact (MK_COMB (@lem1100937 _25328 P EX' _17976 h1) (@lem1100938)). Qed.
Lemma lem1100940 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term21 _25328 EX') = (term22 _25328 _17976).
Proof. exact (fun_ext (fun P : _25328 -> Prop => @lem1100939 _25328 P EX' _17976 h1)). Qed.
Lemma lem1100941 {_25328 : Type'} : (@all (_25328 -> Prop)) = (@all (_25328 -> Prop)).
Proof. exact (eq_refl (@all (_25328 -> Prop))). Qed.
Lemma lem1100942 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term23 _25328 EX') = (term24 _25328 _17976).
Proof. exact (MK_COMB (@lem1100941 _25328) (@lem1100940 _25328 EX' _17976 h1)). Qed.
Lemma lem1100943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1100944 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term25 _25328 EX') = (term26 _25328 _17976).
Proof. exact (MK_COMB (@lem1100943) (@lem1100942 _25328 EX' _17976 h1)). Qed.
Lemma lem1100946 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : EX' = (term4 _25328 _17976).
Proof. exact (h1). Qed.
Lemma lem1100947 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100948 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100946 _25328 EX' _17976 h1) (@lem1100947 _25328 P)). Qed.
Lemma lem1100950 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1100951 {_25328 : Type'} (f : type663 _25328) (y : _25328 -> Prop) : (term6 _25328 f y) = (f y).
Proof. exact (@lem1100950 (_25328 -> Prop) (type1143 _25328) f y). Qed.
Lemma lem1100952 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (@lem1100951 _25328 (term4 _25328 _17976) P). Qed.
Lemma lem1100953 {_25328 : Type'} (_17976 : type1131 _25328) (_17974 : _25328 -> Prop) : (term5 _25328 _17976 _17974) = (term8 _25328 _17976 _17974).
Proof. exact (eq_refl (term5 _25328 _17976 _17974)). Qed.
Lemma lem1100954 {_25328 : Type'} (_17976 : type1131 _25328) : (term9 _25328 _17976) = (term4 _25328 _17976).
Proof. exact (fun_ext (fun _17974 : _25328 -> Prop => @lem1100953 _25328 _17976 _17974)). Qed.
Lemma lem1100955 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100956 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100954 _25328 _17976) (@lem1100955 _25328 P)). Qed.
Lemma lem1100957 {_25328 : Type'} : (@eq ((list _25328) -> Prop)) = (@eq ((list _25328) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25328) -> Prop))). Qed.
Lemma lem1100958 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term10 _25328 _17976 P) = (term11 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100957 _25328) (@lem1100956 _25328 _17976 P)). Qed.
Lemma lem1100959 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (eq_refl (term5 _25328 _17976 P)). Qed.
Lemma lem1100960 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : ((term7 _25328 _17976 P) = (term5 _25328 _17976 P)) = ((term5 _25328 _17976 P) = (term8 _25328 _17976 P)).
Proof. exact (MK_COMB (@lem1100958 _25328 _17976 P) (@lem1100959 _25328 _17976 P)). Qed.
Lemma lem1100961 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (EQ_MP (@lem1100960 _25328 _17976 P) (@lem1100952 _25328 _17976 P)). Qed.
Lemma lem1100962 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term8 _25328 _17976 P).
Proof. exact (TRANS (@lem1100948 _25328 P EX' _17976 h1) (@lem1100961 _25328 _17976 P)). Qed.
Lemma lem1100963 {_25328 : Type'} (h : _25328) (t : list _25328) : (@cons _25328 h t) = (@cons _25328 h t).
Proof. exact (eq_refl (@cons _25328 h t)). Qed.
Lemma lem1100964 {_25328 : Type'} (P : _25328 -> Prop) (h : _25328) (t : list _25328) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term27 _25328 EX' P h t) = (term28 _25328 _17976 P h t).
Proof. exact (MK_COMB (@lem1100962 _25328 P EX' _17976 h1) (@lem1100963 _25328 h t)). Qed.
Lemma lem1100966 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1100967 {_25328 : Type'} (f : type1143 _25328) (y : list _25328) : (term13 _25328 f y) = (f y).
Proof. exact (@lem1100966 (list _25328) Prop f y). Qed.
Lemma lem1100968 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (h : _25328) (t : list _25328) : (term29 _25328 _17976 P h t) = (term28 _25328 _17976 P h t).
Proof. exact (@lem1100967 _25328 (term8 _25328 _17976 P) (@cons _25328 h t)). Qed.
Lemma lem1100969 {_25328 : Type'} (_17976 : type1131 _25328) (_17975 : list _25328) (P : _25328 -> Prop) : (term15 _25328 _17976 P _17975) = (_17976 _17975 P).
Proof. exact (eq_refl (term15 _25328 _17976 P _17975)). Qed.
Lemma lem1100970 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term16 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (fun_ext (fun _17975 : list _25328 => @lem1100969 _25328 _17976 _17975 P)). Qed.
Lemma lem1100971 {_25328 : Type'} (h : _25328) (t : list _25328) : (@cons _25328 h t) = (@cons _25328 h t).
Proof. exact (eq_refl (@cons _25328 h t)). Qed.
Lemma lem1100972 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (h : _25328) (t : list _25328) : (term29 _25328 _17976 P h t) = (term28 _25328 _17976 P h t).
Proof. exact (MK_COMB (@lem1100970 _25328 _17976 P) (@lem1100971 _25328 h t)). Qed.
Lemma lem1100973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100974 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (h : _25328) (t : list _25328) : (term30 _25328 _17976 P h t) = (term31 _25328 _17976 P h t).
Proof. exact (MK_COMB (@lem1100973) (@lem1100972 _25328 _17976 P h t)). Qed.
Lemma lem1100975 {_25328 : Type'} (_17976 : type1131 _25328) (h : _25328) (t : list _25328) (P : _25328 -> Prop) : (term28 _25328 _17976 P h t) = (term32 _25328 _17976 h t P).
Proof. exact (eq_refl (term28 _25328 _17976 P h t)). Qed.
Lemma lem1100976 {_25328 : Type'} (_17976 : type1131 _25328) (h : _25328) (t : list _25328) (P : _25328 -> Prop) : ((term29 _25328 _17976 P h t) = (term28 _25328 _17976 P h t)) = ((term28 _25328 _17976 P h t) = (term32 _25328 _17976 h t P)).
Proof. exact (MK_COMB (@lem1100974 _25328 _17976 P h t) (@lem1100975 _25328 _17976 h t P)). Qed.
Lemma lem1100977 {_25328 : Type'} (_17976 : type1131 _25328) (h : _25328) (t : list _25328) (P : _25328 -> Prop) : (term28 _25328 _17976 P h t) = (term32 _25328 _17976 h t P).
Proof. exact (EQ_MP (@lem1100976 _25328 _17976 h t P) (@lem1100968 _25328 _17976 P h t)). Qed.
Lemma lem1100978 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term27 _25328 EX' P h t) = (term32 _25328 _17976 h t P).
Proof. exact (TRANS (@lem1100964 _25328 P h t EX' _17976 h1) (@lem1100977 _25328 _17976 h t P)). Qed.
Lemma lem1100979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100980 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term33 _25328 EX' P h t) = (term34 _25328 _17976 h t P).
Proof. exact (MK_COMB (@lem1100979) (@lem1100978 _25328 h t P EX' _17976 h1)). Qed.
Lemma lem1100982 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : EX' = (term4 _25328 _17976).
Proof. exact (h1). Qed.
Lemma lem1100983 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100984 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100982 _25328 EX' _17976 h1) (@lem1100983 _25328 P)). Qed.
Lemma lem1100986 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1100987 {_25328 : Type'} (f : type663 _25328) (y : _25328 -> Prop) : (term6 _25328 f y) = (f y).
Proof. exact (@lem1100986 (_25328 -> Prop) (type1143 _25328) f y). Qed.
Lemma lem1100988 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (@lem1100987 _25328 (term4 _25328 _17976) P). Qed.
Lemma lem1100989 {_25328 : Type'} (_17976 : type1131 _25328) (_17974 : _25328 -> Prop) : (term5 _25328 _17976 _17974) = (term8 _25328 _17976 _17974).
Proof. exact (eq_refl (term5 _25328 _17976 _17974)). Qed.
Lemma lem1100990 {_25328 : Type'} (_17976 : type1131 _25328) : (term9 _25328 _17976) = (term4 _25328 _17976).
Proof. exact (fun_ext (fun _17974 : _25328 -> Prop => @lem1100989 _25328 _17976 _17974)). Qed.
Lemma lem1100991 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100992 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term7 _25328 _17976 P) = (term5 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100990 _25328 _17976) (@lem1100991 _25328 P)). Qed.
Lemma lem1100993 {_25328 : Type'} : (@eq ((list _25328) -> Prop)) = (@eq ((list _25328) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25328) -> Prop))). Qed.
Lemma lem1100994 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term10 _25328 _17976 P) = (term11 _25328 _17976 P).
Proof. exact (MK_COMB (@lem1100993 _25328) (@lem1100992 _25328 _17976 P)). Qed.
Lemma lem1100995 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (eq_refl (term5 _25328 _17976 P)). Qed.
Lemma lem1100996 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : ((term7 _25328 _17976 P) = (term5 _25328 _17976 P)) = ((term5 _25328 _17976 P) = (term8 _25328 _17976 P)).
Proof. exact (MK_COMB (@lem1100994 _25328 _17976 P) (@lem1100995 _25328 _17976 P)). Qed.
Lemma lem1100997 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term5 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (EQ_MP (@lem1100996 _25328 _17976 P) (@lem1100988 _25328 _17976 P)). Qed.
Lemma lem1100998 {_25328 : Type'} (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P) = (term8 _25328 _17976 P).
Proof. exact (TRANS (@lem1100984 _25328 P EX' _17976 h1) (@lem1100997 _25328 _17976 P)). Qed.
Lemma lem1100999 {_25328 : Type'} (t : list _25328) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1101000 {_25328 : Type'} (P : _25328 -> Prop) (t : list _25328) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P t) = (term15 _25328 _17976 P t).
Proof. exact (MK_COMB (@lem1100998 _25328 P EX' _17976 h1) (@lem1100999 _25328 t)). Qed.
Lemma lem1101002 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100900 A B f y) (@lem1100899 A B f y)). Qed.
Lemma lem1101003 {_25328 : Type'} (f : type1143 _25328) (y : list _25328) : (term13 _25328 f y) = (f y).
Proof. exact (@lem1101002 (list _25328) Prop f y). Qed.
Lemma lem1101004 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (t : list _25328) : (term35 _25328 _17976 P t) = (term15 _25328 _17976 P t).
Proof. exact (@lem1101003 _25328 (term8 _25328 _17976 P) t). Qed.
Lemma lem1101005 {_25328 : Type'} (_17976 : type1131 _25328) (_17975 : list _25328) (P : _25328 -> Prop) : (term15 _25328 _17976 P _17975) = (_17976 _17975 P).
Proof. exact (eq_refl (term15 _25328 _17976 P _17975)). Qed.
Lemma lem1101006 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term16 _25328 _17976 P) = (term8 _25328 _17976 P).
Proof. exact (fun_ext (fun _17975 : list _25328 => @lem1101005 _25328 _17976 _17975 P)). Qed.
Lemma lem1101007 {_25328 : Type'} (t : list _25328) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1101008 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (t : list _25328) : (term35 _25328 _17976 P t) = (term15 _25328 _17976 P t).
Proof. exact (MK_COMB (@lem1101006 _25328 _17976 P) (@lem1101007 _25328 t)). Qed.
Lemma lem1101009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1101010 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) (t : list _25328) : (term36 _25328 _17976 P t) = (term37 _25328 _17976 P t).
Proof. exact (MK_COMB (@lem1101009) (@lem1101008 _25328 _17976 P t)). Qed.
Lemma lem1101011 {_25328 : Type'} (_17976 : type1131 _25328) (t : list _25328) (P : _25328 -> Prop) : (term15 _25328 _17976 P t) = (_17976 t P).
Proof. exact (eq_refl (term15 _25328 _17976 P t)). Qed.
Lemma lem1101012 {_25328 : Type'} (_17976 : type1131 _25328) (t : list _25328) (P : _25328 -> Prop) : ((term35 _25328 _17976 P t) = (term15 _25328 _17976 P t)) = ((term15 _25328 _17976 P t) = (_17976 t P)).
Proof. exact (MK_COMB (@lem1101010 _25328 _17976 P t) (@lem1101011 _25328 _17976 t P)). Qed.
Lemma lem1101013 {_25328 : Type'} (_17976 : type1131 _25328) (t : list _25328) (P : _25328 -> Prop) : (term15 _25328 _17976 P t) = (_17976 t P).
Proof. exact (EQ_MP (@lem1101012 _25328 _17976 t P) (@lem1101004 _25328 _17976 P t)). Qed.
Lemma lem1101014 {_25328 : Type'} (t : list _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (EX' P t) = (_17976 t P).
Proof. exact (TRANS (@lem1101000 _25328 P t EX' _17976 h1) (@lem1101013 _25328 _17976 t P)). Qed.
Lemma lem1101015 {_25328 : Type'} (P : _25328 -> Prop) (h : _25328) : (term38 _25328 P h) = (term38 _25328 P h).
Proof. exact (eq_refl (term38 _25328 P h)). Qed.
Lemma lem1101016 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term39 _25328 h EX' P t) = (term40 _25328 h _17976 t P).
Proof. exact (MK_COMB (@lem1101015 _25328 P h) (@lem1101014 _25328 t P EX' _17976 h1)). Qed.
Lemma lem1101017 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : ((term27 _25328 EX' P h t) = (term39 _25328 h EX' P t)) = ((term32 _25328 _17976 h t P) = (term40 _25328 h _17976 t P)).
Proof. exact (MK_COMB (@lem1100980 _25328 h t P EX' _17976 h1) (@lem1101016 _25328 h t P EX' _17976 h1)). Qed.
Lemma lem1101018 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term41 _25328 h EX' P) = (term42 _25328 h _17976 P).
Proof. exact (fun_ext (fun t : list _25328 => @lem1101017 _25328 h t P EX' _17976 h1)). Qed.
Lemma lem1101019 {_25328 : Type'} : (@all (list _25328)) = (@all (list _25328)).
Proof. exact (eq_refl (@all (list _25328))). Qed.
Lemma lem1101020 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term43 _25328 h EX' P) = (term44 _25328 h _17976 P).
Proof. exact (MK_COMB (@lem1101019 _25328) (@lem1101018 _25328 h P EX' _17976 h1)). Qed.
Lemma lem1101021 {_25328 : Type'} (h : _25328) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term45 _25328 h EX') = (term46 _25328 h _17976).
Proof. exact (fun_ext (fun P : _25328 -> Prop => @lem1101020 _25328 h P EX' _17976 h1)). Qed.
Lemma lem1101022 {_25328 : Type'} : (@all (_25328 -> Prop)) = (@all (_25328 -> Prop)).
Proof. exact (eq_refl (@all (_25328 -> Prop))). Qed.
Lemma lem1101023 {_25328 : Type'} (h : _25328) (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term47 _25328 h EX') = (term48 _25328 h _17976).
Proof. exact (MK_COMB (@lem1101022 _25328) (@lem1101021 _25328 h EX' _17976 h1)). Qed.
Lemma lem1101024 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term49 _25328 EX') = (term50 _25328 _17976).
Proof. exact (fun_ext (fun h : _25328 => @lem1101023 _25328 h EX' _17976 h1)). Qed.
Lemma lem1101025 {_25328 : Type'} : (@all _25328) = (@all _25328).
Proof. exact (eq_refl (@all _25328)). Qed.
Lemma lem1101026 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term51 _25328 EX') = (term52 _25328 _17976).
Proof. exact (MK_COMB (@lem1101025 _25328) (@lem1101024 _25328 EX' _17976 h1)). Qed.
Lemma lem1101027 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term53 _25328 EX') = (term54 _25328 _17976).
Proof. exact (MK_COMB (@lem1100944 _25328 EX' _17976 h1) (@lem1101026 _25328 EX' _17976 h1)). Qed.
Lemma lem1101028 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : (_17976 (@nil _25328)) = (term55 _25328)) : (_17976 (@nil _25328)) = (term55 _25328).
Proof. exact (h1). Qed.
Lemma lem1101029 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1101030 {_25328 : Type'} (P : _25328 -> Prop) (_17976 : type1131 _25328) (h1 : (_17976 (@nil _25328)) = (term55 _25328)) : (_17976 (@nil _25328) P) = (term56 _25328 P).
Proof. exact (MK_COMB (@lem1101028 _25328 _17976 h1) (@lem1101029 _25328 P)). Qed.
Lemma lem1101031 {_25328 : Type'} (P : _25328 -> Prop) : (term56 _25328 P) = False.
Proof. exact (eq_refl (term56 _25328 P)). Qed.
Lemma lem1101032 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : (term20 _25328 _17976 P) = (term20 _25328 _17976 P).
Proof. exact (eq_refl (term20 _25328 _17976 P)). Qed.
Lemma lem1101033 {_25328 : Type'} (_17976 : type1131 _25328) (P : _25328 -> Prop) : ((_17976 (@nil _25328) P) = (term56 _25328 P)) = ((_17976 (@nil _25328) P) = False).
Proof. exact (MK_COMB (@lem1101032 _25328 _17976 P) (@lem1101031 _25328 P)). Qed.
Lemma lem1101034 {_25328 : Type'} (P : _25328 -> Prop) (_17976 : type1131 _25328) (h1 : (_17976 (@nil _25328)) = (term55 _25328)) : (_17976 (@nil _25328) P) = False.
Proof. exact (EQ_MP (@lem1101033 _25328 _17976 P) (@lem1101030 _25328 P _17976 h1)). Qed.
Lemma lem1101035 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : (_17976 (@nil _25328)) = (term55 _25328)) : term24 _25328 _17976.
Proof. exact (fun P : _25328 -> Prop => @lem1101034 _25328 P _17976 h1). Qed.
Lemma lem1101036 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term57 _25328 _17976.
Proof. exact (h1). Qed.
Lemma lem1101037 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term58 _25328 _17976 h.
Proof. exact (@lem1101036 _25328 _17976 h1 h). Qed.
Lemma lem1101038 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) : (term58 _25328 _17976 h) = (term59 _25328 h _17976).
Proof. exact (eq_refl (term58 _25328 _17976 h)). Qed.
Lemma lem1101039 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term59 _25328 h _17976.
Proof. exact (EQ_MP (@lem1101038 _25328 h _17976) (@lem1101037 _25328 h _17976 h1)). Qed.
Lemma lem1101040 {_25328 : Type'} (h : _25328) (t : list _25328) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term60 _25328 h _17976 t.
Proof. exact (@lem1101039 _25328 h _17976 h1 t). Qed.
Lemma lem1101041 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (t : list _25328) : (term60 _25328 h _17976 t) = ((term61 _25328 _17976 h t) = (term62 _25328 h _17976 t)).
Proof. exact (eq_refl (term60 _25328 h _17976 t)). Qed.
Lemma lem1101042 {_25328 : Type'} (h : _25328) (t : list _25328) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : (term61 _25328 _17976 h t) = (term62 _25328 h _17976 t).
Proof. exact (EQ_MP (@lem1101041 _25328 h _17976 t) (@lem1101040 _25328 h t _17976 h1)). Qed.
Lemma lem1101043 {_25328 : Type'} (P : _25328 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1101044 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : (term32 _25328 _17976 h t P) = (term63 _25328 h _17976 t P).
Proof. exact (MK_COMB (@lem1101042 _25328 h t _17976 h1) (@lem1101043 _25328 P)). Qed.
Lemma lem1101045 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (t : list _25328) (P : _25328 -> Prop) : (term63 _25328 h _17976 t P) = (term40 _25328 h _17976 t P).
Proof. exact (eq_refl (term63 _25328 h _17976 t P)). Qed.
Lemma lem1101046 {_25328 : Type'} (_17976 : type1131 _25328) (h : _25328) (t : list _25328) (P : _25328 -> Prop) : (term34 _25328 _17976 h t P) = (term34 _25328 _17976 h t P).
Proof. exact (eq_refl (term34 _25328 _17976 h t P)). Qed.
Lemma lem1101047 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (t : list _25328) (P : _25328 -> Prop) : ((term32 _25328 _17976 h t P) = (term63 _25328 h _17976 t P)) = ((term32 _25328 _17976 h t P) = (term40 _25328 h _17976 t P)).
Proof. exact (MK_COMB (@lem1101046 _25328 _17976 h t P) (@lem1101045 _25328 h _17976 t P)). Qed.
Lemma lem1101048 {_25328 : Type'} (h : _25328) (t : list _25328) (P : _25328 -> Prop) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : (term32 _25328 _17976 h t P) = (term40 _25328 h _17976 t P).
Proof. exact (EQ_MP (@lem1101047 _25328 h _17976 t P) (@lem1101044 _25328 h t P _17976 h1)). Qed.
Lemma lem1101049 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term44 _25328 h _17976 P.
Proof. exact (fun t : list _25328 => @lem1101048 _25328 h t P _17976 h1). Qed.
Lemma lem1101050 {_25328 : Type'} (h : _25328) (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term48 _25328 h _17976.
Proof. exact (fun P : _25328 -> Prop => @lem1101049 _25328 h P _17976 h1). Qed.
Lemma lem1101051 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term57 _25328 _17976) : term52 _25328 _17976.
Proof. exact (fun h : _25328 => @lem1101050 _25328 h _17976 h1). Qed.
Lemma lem1101052 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term64 _25328 _17976.
Proof. exact (h1). Qed.
Lemma lem1101053 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term57 _25328 _17976.
Proof. exact (proj2 (@lem1101052 _25328 _17976 h1)). Qed.
Lemma lem1101054 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : (_17976 (@nil _25328)) = (term55 _25328).
Proof. exact (proj1 (@lem1101052 _25328 _17976 h1)). Qed.
Lemma lem1101055 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : ((_17976 (@nil _25328)) = (term55 _25328)) = (term24 _25328 _17976).
Proof. exact (prop_ext (fun h2 : (_17976 (@nil _25328)) = (term55 _25328) => @lem1101035 _25328 _17976 h2) (fun h2 : term24 _25328 _17976 => @lem1101054 _25328 _17976 h1)). Qed.
Lemma lem1101056 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term24 _25328 _17976.
Proof. exact (EQ_MP (@lem1101055 _25328 _17976 h1) (@lem1101054 _25328 _17976 h1)). Qed.
Lemma lem1101057 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : (term57 _25328 _17976) = (term52 _25328 _17976).
Proof. exact (prop_ext (fun h2 : term57 _25328 _17976 => @lem1101051 _25328 _17976 h2) (fun h2 : term52 _25328 _17976 => @lem1101053 _25328 _17976 h1)). Qed.
Lemma lem1101058 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term52 _25328 _17976.
Proof. exact (EQ_MP (@lem1101057 _25328 _17976 h1) (@lem1101053 _25328 _17976 h1)). Qed.
Lemma lem1101059 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term54 _25328 _17976.
Proof. exact (conj (@lem1101056 _25328 _17976 h1) (@lem1101058 _25328 _17976 h1)). Qed.
Lemma lem1101060 {A Z : Type'} (NIL' : Z) : term65 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1101061 {A Z : Type'} (NIL' : Z) : (term65 A Z NIL') = (term66 A Z NIL').
Proof. exact (eq_refl (term65 A Z NIL')). Qed.
Lemma lem1101062 {A Z : Type'} (NIL' : Z) : term66 A Z NIL'.
Proof. exact (EQ_MP (@lem1101061 A Z NIL') (@lem1101060 A Z NIL')). Qed.
Lemma lem1101063 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term67 A Z NIL' CONS'.
Proof. exact (@lem1101062 A Z NIL' CONS'). Qed.
Lemma lem1101064 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term67 A Z NIL' CONS') = (term68 A Z NIL' CONS').
Proof. exact (eq_refl (term67 A Z NIL' CONS')). Qed.
Lemma lem1101065 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term68 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1101064 A Z NIL' CONS') (@lem1101063 A Z NIL' CONS')). Qed.
Lemma lem1101066 {_25328 : Type'} (NIL' : type686 _25328) (CONS' : type1387 _25328) : term69 _25328 NIL' CONS'.
Proof. exact (@lem1101065 _25328 (type686 _25328) NIL' CONS'). Qed.
Lemma lem1101067 {_25328 : Type'} : term70 _25328.
Proof. exact (@lem1101066 _25328 (term55 _25328) (term71 _25328)). Qed.
Lemma lem1101068 {_25328 : Type'} (a0 : _25328) : (term72 _25328 a0) = (term73 _25328 a0).
Proof. exact (eq_refl (term72 _25328 a0)). Qed.
Lemma lem1101069 {_25328 : Type'} (a1 : list _25328) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1101070 {_25328 : Type'} (a0 : _25328) (a1 : list _25328) : (term74 _25328 a0 a1) = (term75 _25328 a0 a1).
Proof. exact (MK_COMB (@lem1101068 _25328 a0) (@lem1101069 _25328 a1)). Qed.
Lemma lem1101071 {_25328 : Type'} (a1 : list _25328) (a0 : _25328) : (term75 _25328 a0 a1) = (term76 _25328 a0).
Proof. exact (eq_refl (term75 _25328 a0 a1)). Qed.
Lemma lem1101072 {_25328 : Type'} (a1 : list _25328) (a0 : _25328) : (term74 _25328 a0 a1) = (term76 _25328 a0).
Proof. exact (TRANS (@lem1101070 _25328 a0 a1) (@lem1101071 _25328 a1 a0)). Qed.
Lemma lem1101073 {_25328 : Type'} (fn : type1131 _25328) (a1 : list _25328) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1101074 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) (a1 : list _25328) : (term77 _25328 a0 fn a1) = (term78 _25328 a0 fn a1).
Proof. exact (MK_COMB (@lem1101072 _25328 a1 a0) (@lem1101073 _25328 fn a1)). Qed.
Lemma lem1101075 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) (a1 : list _25328) : (term78 _25328 a0 fn a1) = (term62 _25328 a0 fn a1).
Proof. exact (eq_refl (term78 _25328 a0 fn a1)). Qed.
Lemma lem1101076 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) (a1 : list _25328) : (term77 _25328 a0 fn a1) = (term62 _25328 a0 fn a1).
Proof. exact (TRANS (@lem1101074 _25328 a0 fn a1) (@lem1101075 _25328 a0 fn a1)). Qed.
Lemma lem1101077 {_25328 : Type'} (fn : type1131 _25328) (a0 : _25328) (a1 : list _25328) : (term79 _25328 fn a0 a1) = (term79 _25328 fn a0 a1).
Proof. exact (eq_refl (term79 _25328 fn a0 a1)). Qed.
Lemma lem1101078 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) (a1 : list _25328) : ((term61 _25328 fn a0 a1) = (term77 _25328 a0 fn a1)) = ((term61 _25328 fn a0 a1) = (term62 _25328 a0 fn a1)).
Proof. exact (MK_COMB (@lem1101077 _25328 fn a0 a1) (@lem1101076 _25328 a0 fn a1)). Qed.
Lemma lem1101079 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) : (term80 _25328 a0 fn) = (term81 _25328 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25328 => @lem1101078 _25328 a0 fn a1)). Qed.
Lemma lem1101080 {_25328 : Type'} : (@all (list _25328)) = (@all (list _25328)).
Proof. exact (eq_refl (@all (list _25328))). Qed.
Lemma lem1101081 {_25328 : Type'} (a0 : _25328) (fn : type1131 _25328) : (term82 _25328 a0 fn) = (term59 _25328 a0 fn).
Proof. exact (MK_COMB (@lem1101080 _25328) (@lem1101079 _25328 a0 fn)). Qed.
Lemma lem1101082 {_25328 : Type'} (fn : type1131 _25328) : (term83 _25328 fn) = (term84 _25328 fn).
Proof. exact (fun_ext (fun a0 : _25328 => @lem1101081 _25328 a0 fn)). Qed.
Lemma lem1101083 {_25328 : Type'} : (@all _25328) = (@all _25328).
Proof. exact (eq_refl (@all _25328)). Qed.
Lemma lem1101084 {_25328 : Type'} (fn : type1131 _25328) : (term85 _25328 fn) = (term57 _25328 fn).
Proof. exact (MK_COMB (@lem1101083 _25328) (@lem1101082 _25328 fn)). Qed.
Lemma lem1101085 {_25328 : Type'} (fn : type1131 _25328) : (term86 _25328 fn) = (term86 _25328 fn).
Proof. exact (eq_refl (term86 _25328 fn)). Qed.
Lemma lem1101086 {_25328 : Type'} (fn : type1131 _25328) : (term87 _25328 fn) = (term64 _25328 fn).
Proof. exact (MK_COMB (@lem1101085 _25328 fn) (@lem1101084 _25328 fn)). Qed.
Lemma lem1101087 {_25328 : Type'} : (term88 _25328) = (term89 _25328).
Proof. exact (fun_ext (fun fn : type1131 _25328 => @lem1101086 _25328 fn)). Qed.
Lemma lem1101088 {_25328 : Type'} : (@ex ((list _25328) -> (_25328 -> Prop) -> Prop)) = (@ex ((list _25328) -> (_25328 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25328) -> (_25328 -> Prop) -> Prop))). Qed.
Lemma lem1101089 {_25328 : Type'} : (term70 _25328) = (term90 _25328).
Proof. exact (MK_COMB (@lem1101088 _25328) (@lem1101087 _25328)). Qed.
Lemma lem1101090 {_25328 : Type'} : term90 _25328.
Proof. exact (EQ_MP (@lem1101089 _25328) (@lem1101067 _25328)). Qed.
Lemma lem1101091 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term64 _25328 _17976.
Proof. exact (h1). Qed.
Lemma lem1101092 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term57 _25328 _17976.
Proof. exact (proj2 (@lem1101091 _25328 _17976 h1)). Qed.
Lemma lem1101093 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : (_17976 (@nil _25328)) = (term55 _25328).
Proof. exact (proj1 (@lem1101091 _25328 _17976 h1)). Qed.
Lemma lem1101094 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term64 _25328 _17976.
Proof. exact (conj (@lem1101093 _25328 _17976 h1) (@lem1101092 _25328 _17976 h1)). Qed.
Lemma lem1101095 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term90 _25328.
Proof. exact (ex_intro (term89 _25328) _17976 (@lem1101094 _25328 _17976 h1)). Qed.
Lemma lem1101096 {_25328 : Type'} (h1 : term90 _25328) : term90 _25328.
Proof. exact (h1). Qed.
Lemma lem1101097 {_25328 : Type'} (h1 : term90 _25328) : term90 _25328.
Proof. exact (ex_elim (@lem1101096 _25328 h1) (fun _17976 : type1131 _25328 => fun h0 : term89 _25328 _17976 => @lem1101095 _25328 _17976 h0)). Qed.
Lemma lem1101098 {_25328 : Type'} : (term90 _25328) = (term90 _25328).
Proof. exact (prop_ext (fun h1 : term90 _25328 => @lem1101097 _25328 h1) (fun h1 : term90 _25328 => @lem1101090 _25328)). Qed.
Lemma lem1101099 {_25328 : Type'} : term90 _25328.
Proof. exact (EQ_MP (@lem1101098 _25328) (@lem1101090 _25328)). Qed.
Lemma lem1101100 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term64 _25328 _17976) : term91 _25328.
Proof. exact (ex_intro (term92 _25328) _17976 (@lem1101059 _25328 _17976 h1)). Qed.
Lemma lem1101101 {_25328 : Type'} (h1 : term90 _25328) : term90 _25328.
Proof. exact (h1). Qed.
Lemma lem1101102 {_25328 : Type'} (h1 : term90 _25328) : term91 _25328.
Proof. exact (ex_elim (@lem1101101 _25328 h1) (fun _17976 : type1131 _25328 => fun h0 : term89 _25328 _17976 => @lem1101100 _25328 _17976 h0)). Qed.
Lemma lem1101103 {_25328 : Type'} : (term90 _25328) = (term91 _25328).
Proof. exact (prop_ext (fun h1 : term90 _25328 => @lem1101102 _25328 h1) (fun h1 : term91 _25328 => @lem1101099 _25328)). Qed.
Lemma lem1101104 {_25328 : Type'} : term91 _25328.
Proof. exact (EQ_MP (@lem1101103 _25328) (@lem1101099 _25328)). Qed.
Lemma lem1101105 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) : term54 _25328 _17976.
Proof. exact (h1). Qed.
Lemma lem1101106 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : EX' = (term4 _25328 _17976)) : (term54 _25328 _17976) = (term53 _25328 EX').
Proof. exact (SYM (@lem1101027 _25328 EX' _17976 h1)). Qed.
Lemma lem1101107 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) (h2 : EX' = (term4 _25328 _17976)) : term53 _25328 EX'.
Proof. exact (EQ_MP (@lem1101106 _25328 EX' _17976 h2) (@lem1101105 _25328 _17976 h1)). Qed.
Lemma lem1101108 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) (h2 : EX' = (term4 _25328 _17976)) : term93 _25328.
Proof. exact (ex_intro (term94 _25328) EX' (@lem1101107 _25328 EX' _17976 h1 h2)). Qed.
Lemma lem1101109 {_25328 : Type'} (_17976 : type1131 _25328) : (term4 _25328 _17976) = (term4 _25328 _17976).
Proof. exact (eq_refl (term4 _25328 _17976)). Qed.
Lemma lem1101110 {_25328 : Type'} (EX' : type663 _25328) (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) : term95 _25328 EX' _17976.
Proof. exact (fun h0 : EX' = (term4 _25328 _17976) => @lem1101108 _25328 EX' _17976 h1 h0). Qed.
Lemma lem1101111 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) : term96 _25328 _17976.
Proof. exact (@lem1101110 _25328 (term4 _25328 _17976) _17976 h1). Qed.
Lemma lem1101112 {_25328 : Type'} (_17976 : type1131 _25328) (h1 : term54 _25328 _17976) : term93 _25328.
Proof. exact (@lem1101111 _25328 _17976 h1 (@lem1101109 _25328 _17976)). Qed.
Lemma lem1101113 {_25328 : Type'} (h1 : term91 _25328) : term91 _25328.
Proof. exact (h1). Qed.
Lemma lem1101114 {_25328 : Type'} (h1 : term91 _25328) : term93 _25328.
Proof. exact (ex_elim (@lem1101113 _25328 h1) (fun _17976 : type1131 _25328 => fun h0 : term92 _25328 _17976 => @lem1101112 _25328 _17976 h0)). Qed.
Lemma lem1101115 {_25328 : Type'} : (term91 _25328) = (term93 _25328).
Proof. exact (prop_ext (fun h1 : term91 _25328 => @lem1101114 _25328 h1) (fun h1 : term93 _25328 => @lem1101104 _25328)). Qed.
Lemma lem1101116 {_25328 : Type'} : term93 _25328.
Proof. exact (EQ_MP (@lem1101115 _25328) (@lem1101104 _25328)). Qed.
Lemma lem1101117 {_25328 : Type'} : term97 _25328.
Proof. exact (fun _17980 : prod nat nat => @lem1101116 _25328). Qed.
Lemma lem1101118 {A B : Type'} (P : type1413 A B) : term98 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1101119 {A B : Type'} (P : type1413 A B) : (term98 A B P) = ((term99 A B P) = (term100 A B P)).
Proof. exact (eq_refl (term98 A B P)). Qed.
Lemma lem1101122 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem1101119 A B P) (@lem1101118 A B P)). Qed.
Lemma lem1101123 {_25328 : Type'} (P : type1314 _25328) : (term101 _25328 P) = (term102 _25328 P).
Proof. exact (@lem1101122 (prod nat nat) (type663 _25328) P). Qed.
Lemma lem1101124 {_25328 : Type'} : (term103 _25328) = (term104 _25328).
Proof. exact (@lem1101123 _25328 (term105 _25328)). Qed.
Lemma lem1101125 {_25328 : Type'} (_17980 : prod nat nat) : (term106 _25328 _17980) = (term94 _25328).
Proof. exact (eq_refl (term106 _25328 _17980)). Qed.
Lemma lem1101126 {_25328 : Type'} (EX' : type663 _25328) : EX' = EX'.
Proof. exact (eq_refl EX'). Qed.
Lemma lem1101127 {_25328 : Type'} (_17980 : prod nat nat) (EX' : type663 _25328) : (term107 _25328 _17980 EX') = (term108 _25328 EX').
Proof. exact (MK_COMB (@lem1101125 _25328 _17980) (@lem1101126 _25328 EX')). Qed.
Lemma lem1101128 {_25328 : Type'} (EX' : type663 _25328) : (term108 _25328 EX') = (term53 _25328 EX').
Proof. exact (eq_refl (term108 _25328 EX')). Qed.
Lemma lem1101129 {_25328 : Type'} (_17980 : prod nat nat) (EX' : type663 _25328) : (term107 _25328 _17980 EX') = (term53 _25328 EX').
Proof. exact (TRANS (@lem1101127 _25328 _17980 EX') (@lem1101128 _25328 EX')). Qed.
Lemma lem1101130 {_25328 : Type'} (_17980 : prod nat nat) : (term109 _25328 _17980) = (term94 _25328).
Proof. exact (fun_ext (fun EX' : type663 _25328 => @lem1101129 _25328 _17980 EX')). Qed.
Lemma lem1101131 {_25328 : Type'} : (@ex ((_25328 -> Prop) -> (list _25328) -> Prop)) = (@ex ((_25328 -> Prop) -> (list _25328) -> Prop)).
Proof. exact (eq_refl (@ex ((_25328 -> Prop) -> (list _25328) -> Prop))). Qed.
Lemma lem1101132 {_25328 : Type'} (_17980 : prod nat nat) : (term110 _25328 _17980) = (term93 _25328).
Proof. exact (MK_COMB (@lem1101131 _25328) (@lem1101130 _25328 _17980)). Qed.
Lemma lem1101133 {_25328 : Type'} : (term111 _25328) = (term112 _25328).
Proof. exact (fun_ext (fun _17980 : prod nat nat => @lem1101132 _25328 _17980)). Qed.
Lemma lem1101134 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1101135 {_25328 : Type'} : (term103 _25328) = (term97 _25328).
Proof. exact (MK_COMB (@lem1101134) (@lem1101133 _25328)). Qed.
Lemma lem1101136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1101137 {_25328 : Type'} : (term113 _25328) = (term114 _25328).
Proof. exact (MK_COMB (@lem1101136) (@lem1101135 _25328)). Qed.
Lemma lem1101138 {_25328 : Type'} (_17980 : prod nat nat) : (term106 _25328 _17980) = (term94 _25328).
Proof. exact (eq_refl (term106 _25328 _17980)). Qed.
Lemma lem1101139 {_25328 : Type'} (EX' : type1317 _25328) (_17980 : prod nat nat) : (EX' _17980) = (EX' _17980).
Proof. exact (eq_refl (EX' _17980)). Qed.
Lemma lem1101140 {_25328 : Type'} (EX' : type1317 _25328) (_17980 : prod nat nat) : (term115 _25328 EX' _17980) = (term116 _25328 EX' _17980).
Proof. exact (MK_COMB (@lem1101138 _25328 _17980) (@lem1101139 _25328 EX' _17980)). Qed.
Lemma lem1101141 {_25328 : Type'} (EX' : type1317 _25328) (_17980 : prod nat nat) : (term116 _25328 EX' _17980) = (term117 _25328 EX' _17980).
Proof. exact (eq_refl (term116 _25328 EX' _17980)). Qed.
Lemma lem1101142 {_25328 : Type'} (EX' : type1317 _25328) (_17980 : prod nat nat) : (term115 _25328 EX' _17980) = (term117 _25328 EX' _17980).
Proof. exact (TRANS (@lem1101140 _25328 EX' _17980) (@lem1101141 _25328 EX' _17980)). Qed.
Lemma lem1101143 {_25328 : Type'} (EX' : type1317 _25328) : (term118 _25328 EX') = (term119 _25328 EX').
Proof. exact (fun_ext (fun _17980 : prod nat nat => @lem1101142 _25328 EX' _17980)). Qed.
Lemma lem1101144 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1101145 {_25328 : Type'} (EX' : type1317 _25328) : (term120 _25328 EX') = (term121 _25328 EX').
Proof. exact (MK_COMB (@lem1101144) (@lem1101143 _25328 EX')). Qed.
Lemma lem1101146 {_25328 : Type'} : (term122 _25328) = (term123 _25328).
Proof. exact (fun_ext (fun EX' : type1317 _25328 => @lem1101145 _25328 EX')). Qed.
Lemma lem1101147 {_25328 : Type'} : (@ex ((prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop)) = (@ex ((prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop))). Qed.
Lemma lem1101148 {_25328 : Type'} : (term104 _25328) = (term124 _25328).
Proof. exact (MK_COMB (@lem1101147 _25328) (@lem1101146 _25328)). Qed.
Lemma lem1101149 {_25328 : Type'} : ((term103 _25328) = (term104 _25328)) = ((term97 _25328) = (term124 _25328)).
Proof. exact (MK_COMB (@lem1101137 _25328) (@lem1101148 _25328)). Qed.
Lemma lem1101150 {_25328 : Type'} : (term97 _25328) = (term124 _25328).
Proof. exact (EQ_MP (@lem1101149 _25328) (@lem1101124 _25328)). Qed.
Lemma lem1101151 {_25328 : Type'} : term124 _25328.
Proof. exact (EQ_MP (@lem1101150 _25328) (@lem1101117 _25328)). Qed.
Lemma lem1101153 {A : Type'} : (@ex A) = (term125 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1101154 {_25328 : Type'} : (@ex ((prod nat nat) -> (_25328 -> Prop) -> (list _25328) -> Prop)) = (term126 _25328).
Proof. exact (@lem1101153 (type1317 _25328)). Qed.
Lemma lem1101155 {_25328 : Type'} : (term123 _25328) = (term123 _25328).
Proof. exact (eq_refl (term123 _25328)). Qed.
Lemma lem1101156 {_25328 : Type'} : (term124 _25328) = (term127 _25328).
Proof. exact (MK_COMB (@lem1101154 _25328) (@lem1101155 _25328)). Qed.
Lemma lem1101157 {_25328 : Type'} : (term127 _25328) = (term128 _25328).
Proof. exact (eq_refl (term127 _25328)). Qed.
Lemma lem1101158 {_25328 : Type'} : (term124 _25328) = (term128 _25328).
Proof. exact (TRANS (@lem1101156 _25328) (@lem1101157 _25328)). Qed.
Lemma lem1101159 {_25328 : Type'} : term128 _25328.
Proof. exact (EQ_MP (@lem1101158 _25328) (@lem1101151 _25328)). Qed.
