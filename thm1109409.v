Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109409_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1109078 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1109079 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1109080 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1109079 A B f) (@lem1109078 A B f)). Qed.
Lemma lem1109081 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1109080 A B f y). Qed.
Lemma lem1109082 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1109085 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : ALLPAIRS' = (term4 _25786 _25787 _18046).
Proof. exact (h1). Qed.
Lemma lem1109086 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109087 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109085 _25786 _25787 ALLPAIRS' _18046 h1) (@lem1109086 _25786 _25787 f)). Qed.
Lemma lem1109089 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109090 {_25786 _25787 : Type'} (f : type736 _25786 _25787) (y : type1470 _25786 _25787) : (term6 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109089 (type1470 _25786 _25787) (type1149 _25786 _25787) f y). Qed.
Lemma lem1109091 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (@lem1109090 _25786 _25787 (term4 _25786 _25787 _18046) f). Qed.
Lemma lem1109092 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18043 : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 _18043) = (term8 _25786 _25787 _18046 _18043).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109093 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) : (term9 _25786 _25787 _18046) = (term4 _25786 _25787 _18046).
Proof. exact (fun_ext (fun _18043 : type1470 _25786 _25787 => @lem1109092 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109094 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109095 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109093 _25786 _25787 _18046) (@lem1109094 _25786 _25787 f)). Qed.
Lemma lem1109096 {_25786 _25787 : Type'} : (@eq ((list _25787) -> (list _25786) -> Prop)) = (@eq ((list _25787) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25787) -> (list _25786) -> Prop))). Qed.
Lemma lem1109097 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term10 _25786 _25787 _18046 f) = (term11 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109096 _25786 _25787) (@lem1109095 _25786 _25787 _18046 f)). Qed.
Lemma lem1109098 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 f)). Qed.
Lemma lem1109099 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : ((term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f)) = ((term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f)).
Proof. exact (MK_COMB (@lem1109097 _25786 _25787 _18046 f) (@lem1109098 _25786 _25787 _18046 f)). Qed.
Lemma lem1109100 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (EQ_MP (@lem1109099 _25786 _25787 _18046 f) (@lem1109091 _25786 _25787 _18046 f)). Qed.
Lemma lem1109101 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term8 _25786 _25787 _18046 f).
Proof. exact (TRANS (@lem1109087 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109100 _25786 _25787 _18046 f)). Qed.
Lemma lem1109102 {_25787 : Type'} : (@nil _25787) = (@nil _25787).
Proof. exact (eq_refl (@nil _25787)). Qed.
Lemma lem1109103 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f (@nil _25787)) = (term12 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109101 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109102 _25787)). Qed.
Lemma lem1109105 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109106 {_25786 _25787 : Type'} (f : type1149 _25786 _25787) (y : list _25787) : (term13 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109105 (list _25787) (type1143 _25786) f y). Qed.
Lemma lem1109107 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term14 _25786 _25787 _18046 f) = (term12 _25786 _25787 _18046 f).
Proof. exact (@lem1109106 _25786 _25787 (term8 _25786 _25787 _18046 f) (@nil _25787)). Qed.
Lemma lem1109108 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18044 : list _25787) (f : type1470 _25786 _25787) : (term15 _25786 _25787 _18046 f _18044) = (term16 _25786 _25787 _18046 _18044 f).
Proof. exact (eq_refl (term15 _25786 _25787 _18046 f _18044)). Qed.
Lemma lem1109109 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term17 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (fun_ext (fun _18044 : list _25787 => @lem1109108 _25786 _25787 _18046 _18044 f)). Qed.
Lemma lem1109110 {_25787 : Type'} : (@nil _25787) = (@nil _25787).
Proof. exact (eq_refl (@nil _25787)). Qed.
Lemma lem1109111 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term14 _25786 _25787 _18046 f) = (term12 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109109 _25786 _25787 _18046 f) (@lem1109110 _25787)). Qed.
Lemma lem1109112 {_25786 : Type'} : (@eq ((list _25786) -> Prop)) = (@eq ((list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25786) -> Prop))). Qed.
Lemma lem1109113 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term18 _25786 _25787 _18046 f) = (term19 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109112 _25786) (@lem1109111 _25786 _25787 _18046 f)). Qed.
Lemma lem1109114 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term12 _25786 _25787 _18046 f) = (term20 _25786 _25787 _18046 f).
Proof. exact (eq_refl (term12 _25786 _25787 _18046 f)). Qed.
Lemma lem1109115 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : ((term14 _25786 _25787 _18046 f) = (term12 _25786 _25787 _18046 f)) = ((term12 _25786 _25787 _18046 f) = (term20 _25786 _25787 _18046 f)).
Proof. exact (MK_COMB (@lem1109113 _25786 _25787 _18046 f) (@lem1109114 _25786 _25787 _18046 f)). Qed.
Lemma lem1109116 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term12 _25786 _25787 _18046 f) = (term20 _25786 _25787 _18046 f).
Proof. exact (EQ_MP (@lem1109115 _25786 _25787 _18046 f) (@lem1109107 _25786 _25787 _18046 f)). Qed.
Lemma lem1109117 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f (@nil _25787)) = (term20 _25786 _25787 _18046 f).
Proof. exact (TRANS (@lem1109103 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109116 _25786 _25787 _18046 f)). Qed.
Lemma lem1109118 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109119 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f (@nil _25787) l) = (term21 _25786 _25787 _18046 f l).
Proof. exact (MK_COMB (@lem1109117 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109118 _25786 l)). Qed.
Lemma lem1109121 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109122 {_25786 : Type'} (f : type1143 _25786) (y : list _25786) : (term22 _25786 f y) = (f y).
Proof. exact (@lem1109121 (list _25786) Prop f y). Qed.
Lemma lem1109123 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term23 _25786 _25787 _18046 f l) = (term21 _25786 _25787 _18046 f l).
Proof. exact (@lem1109122 _25786 (term20 _25786 _25787 _18046 f) l). Qed.
Lemma lem1109124 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (_18045 : list _25786) : (term21 _25786 _25787 _18046 f _18045) = (_18046 (@nil _25787) f _18045).
Proof. exact (eq_refl (term21 _25786 _25787 _18046 f _18045)). Qed.
Lemma lem1109125 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term24 _25786 _25787 _18046 f) = (term20 _25786 _25787 _18046 f).
Proof. exact (fun_ext (fun _18045 : list _25786 => @lem1109124 _25786 _25787 _18046 f _18045)). Qed.
Lemma lem1109126 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109127 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term23 _25786 _25787 _18046 f l) = (term21 _25786 _25787 _18046 f l).
Proof. exact (MK_COMB (@lem1109125 _25786 _25787 _18046 f) (@lem1109126 _25786 l)). Qed.
Lemma lem1109128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109129 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term25 _25786 _25787 _18046 f l) = (term26 _25786 _25787 _18046 f l).
Proof. exact (MK_COMB (@lem1109128) (@lem1109127 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109130 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term21 _25786 _25787 _18046 f l) = (_18046 (@nil _25787) f l).
Proof. exact (eq_refl (term21 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109131 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : ((term23 _25786 _25787 _18046 f l) = (term21 _25786 _25787 _18046 f l)) = ((term21 _25786 _25787 _18046 f l) = (_18046 (@nil _25787) f l)).
Proof. exact (MK_COMB (@lem1109129 _25786 _25787 _18046 f l) (@lem1109130 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109132 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term21 _25786 _25787 _18046 f l) = (_18046 (@nil _25787) f l).
Proof. exact (EQ_MP (@lem1109131 _25786 _25787 _18046 f l) (@lem1109123 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109133 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f (@nil _25787) l) = (_18046 (@nil _25787) f l).
Proof. exact (TRANS (@lem1109119 _25786 _25787 f l ALLPAIRS' _18046 h1) (@lem1109132 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109135 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term27 _25786 _25787 ALLPAIRS' f l) = (term28 _25786 _25787 _18046 f l).
Proof. exact (MK_COMB (@lem1109134) (@lem1109133 _25786 _25787 f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109136 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1109137 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : ((ALLPAIRS' f (@nil _25787) l) = True) = ((_18046 (@nil _25787) f l) = True).
Proof. exact (MK_COMB (@lem1109135 _25786 _25787 f l ALLPAIRS' _18046 h1) (@lem1109136)). Qed.
Lemma lem1109138 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term29 _25786 _25787 ALLPAIRS' f) = (term30 _25786 _25787 _18046 f).
Proof. exact (fun_ext (fun l : list _25786 => @lem1109137 _25786 _25787 f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109139 {_25786 : Type'} : (@all (list _25786)) = (@all (list _25786)).
Proof. exact (eq_refl (@all (list _25786))). Qed.
Lemma lem1109140 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term31 _25786 _25787 ALLPAIRS' f) = (term32 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109139 _25786) (@lem1109138 _25786 _25787 f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109141 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term33 _25786 _25787 ALLPAIRS') = (term34 _25786 _25787 _18046).
Proof. exact (fun_ext (fun f : type1470 _25786 _25787 => @lem1109140 _25786 _25787 f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109142 {_25786 _25787 : Type'} : (@all (_25787 -> _25786 -> Prop)) = (@all (_25787 -> _25786 -> Prop)).
Proof. exact (eq_refl (@all (_25787 -> _25786 -> Prop))). Qed.
Lemma lem1109143 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term35 _25786 _25787 ALLPAIRS') = (term36 _25786 _25787 _18046).
Proof. exact (MK_COMB (@lem1109142 _25786 _25787) (@lem1109141 _25786 _25787 ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1109145 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term37 _25786 _25787 ALLPAIRS') = (term38 _25786 _25787 _18046).
Proof. exact (MK_COMB (@lem1109144) (@lem1109143 _25786 _25787 ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109147 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : ALLPAIRS' = (term4 _25786 _25787 _18046).
Proof. exact (h1). Qed.
Lemma lem1109148 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109149 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109147 _25786 _25787 ALLPAIRS' _18046 h1) (@lem1109148 _25786 _25787 f)). Qed.
Lemma lem1109151 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109152 {_25786 _25787 : Type'} (f : type736 _25786 _25787) (y : type1470 _25786 _25787) : (term6 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109151 (type1470 _25786 _25787) (type1149 _25786 _25787) f y). Qed.
Lemma lem1109153 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (@lem1109152 _25786 _25787 (term4 _25786 _25787 _18046) f). Qed.
Lemma lem1109154 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18043 : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 _18043) = (term8 _25786 _25787 _18046 _18043).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109155 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) : (term9 _25786 _25787 _18046) = (term4 _25786 _25787 _18046).
Proof. exact (fun_ext (fun _18043 : type1470 _25786 _25787 => @lem1109154 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109156 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109157 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109155 _25786 _25787 _18046) (@lem1109156 _25786 _25787 f)). Qed.
Lemma lem1109158 {_25786 _25787 : Type'} : (@eq ((list _25787) -> (list _25786) -> Prop)) = (@eq ((list _25787) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25787) -> (list _25786) -> Prop))). Qed.
Lemma lem1109159 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term10 _25786 _25787 _18046 f) = (term11 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109158 _25786 _25787) (@lem1109157 _25786 _25787 _18046 f)). Qed.
Lemma lem1109160 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 f)). Qed.
Lemma lem1109161 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : ((term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f)) = ((term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f)).
Proof. exact (MK_COMB (@lem1109159 _25786 _25787 _18046 f) (@lem1109160 _25786 _25787 _18046 f)). Qed.
Lemma lem1109162 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (EQ_MP (@lem1109161 _25786 _25787 _18046 f) (@lem1109153 _25786 _25787 _18046 f)). Qed.
Lemma lem1109163 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term8 _25786 _25787 _18046 f).
Proof. exact (TRANS (@lem1109149 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109162 _25786 _25787 _18046 f)). Qed.
Lemma lem1109164 {_25787 : Type'} (h : _25787) (t : list _25787) : (@cons _25787 h t) = (@cons _25787 h t).
Proof. exact (eq_refl (@cons _25787 h t)). Qed.
Lemma lem1109165 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term39 _25786 _25787 ALLPAIRS' f h t) = (term40 _25786 _25787 _18046 f h t).
Proof. exact (MK_COMB (@lem1109163 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109164 _25787 h t)). Qed.
Lemma lem1109167 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109168 {_25786 _25787 : Type'} (f : type1149 _25786 _25787) (y : list _25787) : (term13 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109167 (list _25787) (type1143 _25786) f y). Qed.
Lemma lem1109169 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) : (term41 _25786 _25787 _18046 f h t) = (term40 _25786 _25787 _18046 f h t).
Proof. exact (@lem1109168 _25786 _25787 (term8 _25786 _25787 _18046 f) (@cons _25787 h t)). Qed.
Lemma lem1109170 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18044 : list _25787) (f : type1470 _25786 _25787) : (term15 _25786 _25787 _18046 f _18044) = (term16 _25786 _25787 _18046 _18044 f).
Proof. exact (eq_refl (term15 _25786 _25787 _18046 f _18044)). Qed.
Lemma lem1109171 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term17 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (fun_ext (fun _18044 : list _25787 => @lem1109170 _25786 _25787 _18046 _18044 f)). Qed.
Lemma lem1109172 {_25787 : Type'} (h : _25787) (t : list _25787) : (@cons _25787 h t) = (@cons _25787 h t).
Proof. exact (eq_refl (@cons _25787 h t)). Qed.
Lemma lem1109173 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) : (term41 _25786 _25787 _18046 f h t) = (term40 _25786 _25787 _18046 f h t).
Proof. exact (MK_COMB (@lem1109171 _25786 _25787 _18046 f) (@lem1109172 _25787 h t)). Qed.
Lemma lem1109174 {_25786 : Type'} : (@eq ((list _25786) -> Prop)) = (@eq ((list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25786) -> Prop))). Qed.
Lemma lem1109175 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) : (term42 _25786 _25787 _18046 f h t) = (term43 _25786 _25787 _18046 f h t).
Proof. exact (MK_COMB (@lem1109174 _25786) (@lem1109173 _25786 _25787 _18046 f h t)). Qed.
Lemma lem1109176 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term40 _25786 _25787 _18046 f h t) = (term44 _25786 _25787 _18046 h t f).
Proof. exact (eq_refl (term40 _25786 _25787 _18046 f h t)). Qed.
Lemma lem1109177 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) : ((term41 _25786 _25787 _18046 f h t) = (term40 _25786 _25787 _18046 f h t)) = ((term40 _25786 _25787 _18046 f h t) = (term44 _25786 _25787 _18046 h t f)).
Proof. exact (MK_COMB (@lem1109175 _25786 _25787 _18046 f h t) (@lem1109176 _25786 _25787 _18046 h t f)). Qed.
Lemma lem1109178 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term40 _25786 _25787 _18046 f h t) = (term44 _25786 _25787 _18046 h t f).
Proof. exact (EQ_MP (@lem1109177 _25786 _25787 _18046 h t f) (@lem1109169 _25786 _25787 _18046 f h t)). Qed.
Lemma lem1109179 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term39 _25786 _25787 ALLPAIRS' f h t) = (term44 _25786 _25787 _18046 h t f).
Proof. exact (TRANS (@lem1109165 _25786 _25787 f h t ALLPAIRS' _18046 h1) (@lem1109178 _25786 _25787 _18046 h t f)). Qed.
Lemma lem1109180 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109181 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term45 _25786 _25787 ALLPAIRS' f h t l) = (term46 _25786 _25787 _18046 h t f l).
Proof. exact (MK_COMB (@lem1109179 _25786 _25787 h t f ALLPAIRS' _18046 h1) (@lem1109180 _25786 l)). Qed.
Lemma lem1109183 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109184 {_25786 : Type'} (f : type1143 _25786) (y : list _25786) : (term22 _25786 f y) = (f y).
Proof. exact (@lem1109183 (list _25786) Prop f y). Qed.
Lemma lem1109185 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term47 _25786 _25787 _18046 h t f l) = (term46 _25786 _25787 _18046 h t f l).
Proof. exact (@lem1109184 _25786 (term44 _25786 _25787 _18046 h t f) l). Qed.
Lemma lem1109186 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (_18045 : list _25786) : (term46 _25786 _25787 _18046 h t f _18045) = (term48 _25786 _25787 _18046 h t f _18045).
Proof. exact (eq_refl (term46 _25786 _25787 _18046 h t f _18045)). Qed.
Lemma lem1109187 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term49 _25786 _25787 _18046 h t f) = (term44 _25786 _25787 _18046 h t f).
Proof. exact (fun_ext (fun _18045 : list _25786 => @lem1109186 _25786 _25787 _18046 h t f _18045)). Qed.
Lemma lem1109188 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109189 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term47 _25786 _25787 _18046 h t f l) = (term46 _25786 _25787 _18046 h t f l).
Proof. exact (MK_COMB (@lem1109187 _25786 _25787 _18046 h t f) (@lem1109188 _25786 l)). Qed.
Lemma lem1109190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109191 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term50 _25786 _25787 _18046 h t f l) = (term51 _25786 _25787 _18046 h t f l).
Proof. exact (MK_COMB (@lem1109190) (@lem1109189 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109192 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term46 _25786 _25787 _18046 h t f l) = (term48 _25786 _25787 _18046 h t f l).
Proof. exact (eq_refl (term46 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109193 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : ((term47 _25786 _25787 _18046 h t f l) = (term46 _25786 _25787 _18046 h t f l)) = ((term46 _25786 _25787 _18046 h t f l) = (term48 _25786 _25787 _18046 h t f l)).
Proof. exact (MK_COMB (@lem1109191 _25786 _25787 _18046 h t f l) (@lem1109192 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109194 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term46 _25786 _25787 _18046 h t f l) = (term48 _25786 _25787 _18046 h t f l).
Proof. exact (EQ_MP (@lem1109193 _25786 _25787 _18046 h t f l) (@lem1109185 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109195 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term45 _25786 _25787 ALLPAIRS' f h t l) = (term48 _25786 _25787 _18046 h t f l).
Proof. exact (TRANS (@lem1109181 _25786 _25787 h t f l ALLPAIRS' _18046 h1) (@lem1109194 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109197 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term52 _25786 _25787 ALLPAIRS' f h t l) = (term53 _25786 _25787 _18046 h t f l).
Proof. exact (MK_COMB (@lem1109196) (@lem1109195 _25786 _25787 h t f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109199 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : ALLPAIRS' = (term4 _25786 _25787 _18046).
Proof. exact (h1). Qed.
Lemma lem1109200 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109201 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109199 _25786 _25787 ALLPAIRS' _18046 h1) (@lem1109200 _25786 _25787 f)). Qed.
Lemma lem1109203 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109204 {_25786 _25787 : Type'} (f : type736 _25786 _25787) (y : type1470 _25786 _25787) : (term6 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109203 (type1470 _25786 _25787) (type1149 _25786 _25787) f y). Qed.
Lemma lem1109205 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (@lem1109204 _25786 _25787 (term4 _25786 _25787 _18046) f). Qed.
Lemma lem1109206 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18043 : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 _18043) = (term8 _25786 _25787 _18046 _18043).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109207 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) : (term9 _25786 _25787 _18046) = (term4 _25786 _25787 _18046).
Proof. exact (fun_ext (fun _18043 : type1470 _25786 _25787 => @lem1109206 _25786 _25787 _18046 _18043)). Qed.
Lemma lem1109208 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109209 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109207 _25786 _25787 _18046) (@lem1109208 _25786 _25787 f)). Qed.
Lemma lem1109210 {_25786 _25787 : Type'} : (@eq ((list _25787) -> (list _25786) -> Prop)) = (@eq ((list _25787) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25787) -> (list _25786) -> Prop))). Qed.
Lemma lem1109211 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term10 _25786 _25787 _18046 f) = (term11 _25786 _25787 _18046 f).
Proof. exact (MK_COMB (@lem1109210 _25786 _25787) (@lem1109209 _25786 _25787 _18046 f)). Qed.
Lemma lem1109212 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (eq_refl (term5 _25786 _25787 _18046 f)). Qed.
Lemma lem1109213 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : ((term7 _25786 _25787 _18046 f) = (term5 _25786 _25787 _18046 f)) = ((term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f)).
Proof. exact (MK_COMB (@lem1109211 _25786 _25787 _18046 f) (@lem1109212 _25786 _25787 _18046 f)). Qed.
Lemma lem1109214 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term5 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (EQ_MP (@lem1109213 _25786 _25787 _18046 f) (@lem1109205 _25786 _25787 _18046 f)). Qed.
Lemma lem1109215 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f) = (term8 _25786 _25787 _18046 f).
Proof. exact (TRANS (@lem1109201 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109214 _25786 _25787 _18046 f)). Qed.
Lemma lem1109216 {_25787 : Type'} (t : list _25787) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1109217 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (t : list _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f t) = (term15 _25786 _25787 _18046 f t).
Proof. exact (MK_COMB (@lem1109215 _25786 _25787 f ALLPAIRS' _18046 h1) (@lem1109216 _25787 t)). Qed.
Lemma lem1109219 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109220 {_25786 _25787 : Type'} (f : type1149 _25786 _25787) (y : list _25787) : (term13 _25786 _25787 f y) = (f y).
Proof. exact (@lem1109219 (list _25787) (type1143 _25786) f y). Qed.
Lemma lem1109221 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term54 _25786 _25787 _18046 f t) = (term15 _25786 _25787 _18046 f t).
Proof. exact (@lem1109220 _25786 _25787 (term8 _25786 _25787 _18046 f) t). Qed.
Lemma lem1109222 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (_18044 : list _25787) (f : type1470 _25786 _25787) : (term15 _25786 _25787 _18046 f _18044) = (term16 _25786 _25787 _18046 _18044 f).
Proof. exact (eq_refl (term15 _25786 _25787 _18046 f _18044)). Qed.
Lemma lem1109223 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term17 _25786 _25787 _18046 f) = (term8 _25786 _25787 _18046 f).
Proof. exact (fun_ext (fun _18044 : list _25787 => @lem1109222 _25786 _25787 _18046 _18044 f)). Qed.
Lemma lem1109224 {_25787 : Type'} (t : list _25787) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1109225 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term54 _25786 _25787 _18046 f t) = (term15 _25786 _25787 _18046 f t).
Proof. exact (MK_COMB (@lem1109223 _25786 _25787 _18046 f) (@lem1109224 _25787 t)). Qed.
Lemma lem1109226 {_25786 : Type'} : (@eq ((list _25786) -> Prop)) = (@eq ((list _25786) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25786) -> Prop))). Qed.
Lemma lem1109227 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term55 _25786 _25787 _18046 f t) = (term56 _25786 _25787 _18046 f t).
Proof. exact (MK_COMB (@lem1109226 _25786) (@lem1109225 _25786 _25787 _18046 f t)). Qed.
Lemma lem1109228 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term15 _25786 _25787 _18046 f t) = (term16 _25786 _25787 _18046 t f).
Proof. exact (eq_refl (term15 _25786 _25787 _18046 f t)). Qed.
Lemma lem1109229 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : ((term54 _25786 _25787 _18046 f t) = (term15 _25786 _25787 _18046 f t)) = ((term15 _25786 _25787 _18046 f t) = (term16 _25786 _25787 _18046 t f)).
Proof. exact (MK_COMB (@lem1109227 _25786 _25787 _18046 f t) (@lem1109228 _25786 _25787 _18046 t f)). Qed.
Lemma lem1109230 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term15 _25786 _25787 _18046 f t) = (term16 _25786 _25787 _18046 t f).
Proof. exact (EQ_MP (@lem1109229 _25786 _25787 _18046 t f) (@lem1109221 _25786 _25787 _18046 f t)). Qed.
Lemma lem1109231 {_25786 _25787 : Type'} (t : list _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f t) = (term16 _25786 _25787 _18046 t f).
Proof. exact (TRANS (@lem1109217 _25786 _25787 f t ALLPAIRS' _18046 h1) (@lem1109230 _25786 _25787 _18046 t f)). Qed.
Lemma lem1109232 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109233 {_25786 _25787 : Type'} (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f t l) = (term57 _25786 _25787 _18046 t f l).
Proof. exact (MK_COMB (@lem1109231 _25786 _25787 t f ALLPAIRS' _18046 h1) (@lem1109232 _25786 l)). Qed.
Lemma lem1109235 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1109082 A B f y) (@lem1109081 A B f y)). Qed.
Lemma lem1109236 {_25786 : Type'} (f : type1143 _25786) (y : list _25786) : (term22 _25786 f y) = (f y).
Proof. exact (@lem1109235 (list _25786) Prop f y). Qed.
Lemma lem1109237 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term58 _25786 _25787 _18046 t f l) = (term57 _25786 _25787 _18046 t f l).
Proof. exact (@lem1109236 _25786 (term16 _25786 _25787 _18046 t f) l). Qed.
Lemma lem1109238 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (_18045 : list _25786) : (term57 _25786 _25787 _18046 t f _18045) = (_18046 t f _18045).
Proof. exact (eq_refl (term57 _25786 _25787 _18046 t f _18045)). Qed.
Lemma lem1109239 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term59 _25786 _25787 _18046 t f) = (term16 _25786 _25787 _18046 t f).
Proof. exact (fun_ext (fun _18045 : list _25786 => @lem1109238 _25786 _25787 _18046 t f _18045)). Qed.
Lemma lem1109240 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109241 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term58 _25786 _25787 _18046 t f l) = (term57 _25786 _25787 _18046 t f l).
Proof. exact (MK_COMB (@lem1109239 _25786 _25787 _18046 t f) (@lem1109240 _25786 l)). Qed.
Lemma lem1109242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109243 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term60 _25786 _25787 _18046 t f l) = (term61 _25786 _25787 _18046 t f l).
Proof. exact (MK_COMB (@lem1109242) (@lem1109241 _25786 _25787 _18046 t f l)). Qed.
Lemma lem1109244 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term57 _25786 _25787 _18046 t f l) = (_18046 t f l).
Proof. exact (eq_refl (term57 _25786 _25787 _18046 t f l)). Qed.
Lemma lem1109245 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : ((term58 _25786 _25787 _18046 t f l) = (term57 _25786 _25787 _18046 t f l)) = ((term57 _25786 _25787 _18046 t f l) = (_18046 t f l)).
Proof. exact (MK_COMB (@lem1109243 _25786 _25787 _18046 t f l) (@lem1109244 _25786 _25787 _18046 t f l)). Qed.
Lemma lem1109246 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term57 _25786 _25787 _18046 t f l) = (_18046 t f l).
Proof. exact (EQ_MP (@lem1109245 _25786 _25787 _18046 t f l) (@lem1109237 _25786 _25787 _18046 t f l)). Qed.
Lemma lem1109247 {_25786 _25787 : Type'} (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (ALLPAIRS' f t l) = (_18046 t f l).
Proof. exact (TRANS (@lem1109233 _25786 _25787 t f l ALLPAIRS' _18046 h1) (@lem1109246 _25786 _25787 _18046 t f l)). Qed.
Lemma lem1109248 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (l : list _25786) : (term62 _25786 _25787 f h l) = (term62 _25786 _25787 f h l).
Proof. exact (eq_refl (term62 _25786 _25787 f h l)). Qed.
Lemma lem1109249 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term63 _25786 _25787 h ALLPAIRS' f t l) = (term64 _25786 _25787 h _18046 t f l).
Proof. exact (MK_COMB (@lem1109248 _25786 _25787 f h l) (@lem1109247 _25786 _25787 t f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109250 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : ((term45 _25786 _25787 ALLPAIRS' f h t l) = (term63 _25786 _25787 h ALLPAIRS' f t l)) = ((term48 _25786 _25787 _18046 h t f l) = (term64 _25786 _25787 h _18046 t f l)).
Proof. exact (MK_COMB (@lem1109197 _25786 _25787 h t f l ALLPAIRS' _18046 h1) (@lem1109249 _25786 _25787 h t f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109251 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term65 _25786 _25787 h ALLPAIRS' f t) = (term66 _25786 _25787 h _18046 t f).
Proof. exact (fun_ext (fun l : list _25786 => @lem1109250 _25786 _25787 h t f l ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109252 {_25786 : Type'} : (@all (list _25786)) = (@all (list _25786)).
Proof. exact (eq_refl (@all (list _25786))). Qed.
Lemma lem1109253 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term67 _25786 _25787 h ALLPAIRS' f t) = (term68 _25786 _25787 h _18046 t f).
Proof. exact (MK_COMB (@lem1109252 _25786) (@lem1109251 _25786 _25787 h t f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109254 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term69 _25786 _25787 h ALLPAIRS' f) = (term70 _25786 _25787 h _18046 f).
Proof. exact (fun_ext (fun t : list _25787 => @lem1109253 _25786 _25787 h t f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109255 {_25787 : Type'} : (@all (list _25787)) = (@all (list _25787)).
Proof. exact (eq_refl (@all (list _25787))). Qed.
Lemma lem1109256 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term71 _25786 _25787 h ALLPAIRS' f) = (term72 _25786 _25787 h _18046 f).
Proof. exact (MK_COMB (@lem1109255 _25787) (@lem1109254 _25786 _25787 h f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109257 {_25786 _25787 : Type'} (h : _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term73 _25786 _25787 h ALLPAIRS') = (term74 _25786 _25787 h _18046).
Proof. exact (fun_ext (fun f : type1470 _25786 _25787 => @lem1109256 _25786 _25787 h f ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109258 {_25786 _25787 : Type'} : (@all (_25787 -> _25786 -> Prop)) = (@all (_25787 -> _25786 -> Prop)).
Proof. exact (eq_refl (@all (_25787 -> _25786 -> Prop))). Qed.
Lemma lem1109259 {_25786 _25787 : Type'} (h : _25787) (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term75 _25786 _25787 h ALLPAIRS') = (term76 _25786 _25787 h _18046).
Proof. exact (MK_COMB (@lem1109258 _25786 _25787) (@lem1109257 _25786 _25787 h ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109260 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term77 _25786 _25787 ALLPAIRS') = (term78 _25786 _25787 _18046).
Proof. exact (fun_ext (fun h : _25787 => @lem1109259 _25786 _25787 h ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109261 {_25787 : Type'} : (@all _25787) = (@all _25787).
Proof. exact (eq_refl (@all _25787)). Qed.
Lemma lem1109262 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term79 _25786 _25787 ALLPAIRS') = (term80 _25786 _25787 _18046).
Proof. exact (MK_COMB (@lem1109261 _25787) (@lem1109260 _25786 _25787 ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109263 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term81 _25786 _25787 ALLPAIRS') = (term82 _25786 _25787 _18046).
Proof. exact (MK_COMB (@lem1109145 _25786 _25787 ALLPAIRS' _18046 h1) (@lem1109262 _25786 _25787 ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109264 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : (_18046 (@nil _25787)) = (term83 _25786 _25787).
Proof. exact (h1). Qed.
Lemma lem1109265 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109266 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : (_18046 (@nil _25787) f) = (term84 _25786 _25787 f).
Proof. exact (MK_COMB (@lem1109264 _25786 _25787 _18046 h1) (@lem1109265 _25786 _25787 f)). Qed.
Lemma lem1109267 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term84 _25786 _25787 f) = (term85 _25786).
Proof. exact (eq_refl (term84 _25786 _25787 f)). Qed.
Lemma lem1109268 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : (term86 _25786 _25787 _18046 f) = (term86 _25786 _25787 _18046 f).
Proof. exact (eq_refl (term86 _25786 _25787 _18046 f)). Qed.
Lemma lem1109269 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) : ((_18046 (@nil _25787) f) = (term84 _25786 _25787 f)) = ((_18046 (@nil _25787) f) = (term85 _25786)).
Proof. exact (MK_COMB (@lem1109268 _25786 _25787 _18046 f) (@lem1109267 _25786 _25787 f)). Qed.
Lemma lem1109270 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : (_18046 (@nil _25787) f) = (term85 _25786).
Proof. exact (EQ_MP (@lem1109269 _25786 _25787 _18046 f) (@lem1109266 _25786 _25787 f _18046 h1)). Qed.
Lemma lem1109271 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109272 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : (_18046 (@nil _25787) f l) = (term87 _25786 l).
Proof. exact (MK_COMB (@lem1109270 _25786 _25787 f _18046 h1) (@lem1109271 _25786 l)). Qed.
Lemma lem1109273 {_25786 : Type'} (l : list _25786) : (term87 _25786 l) = True.
Proof. exact (eq_refl (term87 _25786 l)). Qed.
Lemma lem1109274 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term28 _25786 _25787 _18046 f l) = (term28 _25786 _25787 _18046 f l).
Proof. exact (eq_refl (term28 _25786 _25787 _18046 f l)). Qed.
Lemma lem1109275 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (f : type1470 _25786 _25787) (l : list _25786) : ((_18046 (@nil _25787) f l) = (term87 _25786 l)) = ((_18046 (@nil _25787) f l) = True).
Proof. exact (MK_COMB (@lem1109274 _25786 _25787 _18046 f l) (@lem1109273 _25786 l)). Qed.
Lemma lem1109276 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : (_18046 (@nil _25787) f l) = True.
Proof. exact (EQ_MP (@lem1109275 _25786 _25787 _18046 f l) (@lem1109272 _25786 _25787 f l _18046 h1)). Qed.
Lemma lem1109277 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : term32 _25786 _25787 _18046 f.
Proof. exact (fun l : list _25786 => @lem1109276 _25786 _25787 f l _18046 h1). Qed.
Lemma lem1109278 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : (_18046 (@nil _25787)) = (term83 _25786 _25787)) : term36 _25786 _25787 _18046.
Proof. exact (fun f : type1470 _25786 _25787 => @lem1109277 _25786 _25787 f _18046 h1). Qed.
Lemma lem1109279 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term88 _25786 _25787 _18046.
Proof. exact (h1). Qed.
Lemma lem1109280 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term89 _25786 _25787 _18046 h.
Proof. exact (@lem1109279 _25786 _25787 _18046 h1 h). Qed.
Lemma lem1109281 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) : (term89 _25786 _25787 _18046 h) = (term90 _25786 _25787 h _18046).
Proof. exact (eq_refl (term89 _25786 _25787 _18046 h)). Qed.
Lemma lem1109282 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term90 _25786 _25787 h _18046.
Proof. exact (EQ_MP (@lem1109281 _25786 _25787 h _18046) (@lem1109280 _25786 _25787 h _18046 h1)). Qed.
Lemma lem1109283 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term91 _25786 _25787 h _18046 t.
Proof. exact (@lem1109282 _25786 _25787 h _18046 h1 t). Qed.
Lemma lem1109284 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (t : list _25787) : (term91 _25786 _25787 h _18046 t) = ((term92 _25786 _25787 _18046 h t) = (term93 _25786 _25787 h _18046 t)).
Proof. exact (eq_refl (term91 _25786 _25787 h _18046 t)). Qed.
Lemma lem1109285 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : (term92 _25786 _25787 _18046 h t) = (term93 _25786 _25787 h _18046 t).
Proof. exact (EQ_MP (@lem1109284 _25786 _25787 h _18046 t) (@lem1109283 _25786 _25787 h t _18046 h1)). Qed.
Lemma lem1109286 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109287 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : (term94 _25786 _25787 _18046 h t f) = (term95 _25786 _25787 h _18046 t f).
Proof. exact (MK_COMB (@lem1109285 _25786 _25787 h t _18046 h1) (@lem1109286 _25786 _25787 f)). Qed.
Lemma lem1109288 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term95 _25786 _25787 h _18046 t f) = (term96 _25786 _25787 h _18046 t f).
Proof. exact (eq_refl (term95 _25786 _25787 h _18046 t f)). Qed.
Lemma lem1109289 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) : (term97 _25786 _25787 _18046 h t f) = (term97 _25786 _25787 _18046 h t f).
Proof. exact (eq_refl (term97 _25786 _25787 _18046 h t f)). Qed.
Lemma lem1109290 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) : ((term94 _25786 _25787 _18046 h t f) = (term95 _25786 _25787 h _18046 t f)) = ((term94 _25786 _25787 _18046 h t f) = (term96 _25786 _25787 h _18046 t f)).
Proof. exact (MK_COMB (@lem1109289 _25786 _25787 _18046 h t f) (@lem1109288 _25786 _25787 h _18046 t f)). Qed.
Lemma lem1109291 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : (term94 _25786 _25787 _18046 h t f) = (term96 _25786 _25787 h _18046 t f).
Proof. exact (EQ_MP (@lem1109290 _25786 _25787 h _18046 t f) (@lem1109287 _25786 _25787 h t f _18046 h1)). Qed.
Lemma lem1109292 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109293 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : (term48 _25786 _25787 _18046 h t f l) = (term98 _25786 _25787 h _18046 t f l).
Proof. exact (MK_COMB (@lem1109291 _25786 _25787 h t f _18046 h1) (@lem1109292 _25786 l)). Qed.
Lemma lem1109294 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term98 _25786 _25787 h _18046 t f l) = (term64 _25786 _25787 h _18046 t f l).
Proof. exact (eq_refl (term98 _25786 _25787 h _18046 t f l)). Qed.
Lemma lem1109295 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : (term53 _25786 _25787 _18046 h t f l) = (term53 _25786 _25787 _18046 h t f l).
Proof. exact (eq_refl (term53 _25786 _25787 _18046 h t f l)). Qed.
Lemma lem1109296 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) : ((term48 _25786 _25787 _18046 h t f l) = (term98 _25786 _25787 h _18046 t f l)) = ((term48 _25786 _25787 _18046 h t f l) = (term64 _25786 _25787 h _18046 t f l)).
Proof. exact (MK_COMB (@lem1109295 _25786 _25787 _18046 h t f l) (@lem1109294 _25786 _25787 h _18046 t f l)). Qed.
Lemma lem1109297 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (l : list _25786) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : (term48 _25786 _25787 _18046 h t f l) = (term64 _25786 _25787 h _18046 t f l).
Proof. exact (EQ_MP (@lem1109296 _25786 _25787 h _18046 t f l) (@lem1109293 _25786 _25787 h t f l _18046 h1)). Qed.
Lemma lem1109298 {_25786 _25787 : Type'} (h : _25787) (t : list _25787) (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term68 _25786 _25787 h _18046 t f.
Proof. exact (fun l : list _25786 => @lem1109297 _25786 _25787 h t f l _18046 h1). Qed.
Lemma lem1109299 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term72 _25786 _25787 h _18046 f.
Proof. exact (fun t : list _25787 => @lem1109298 _25786 _25787 h t f _18046 h1). Qed.
Lemma lem1109300 {_25786 _25787 : Type'} (h : _25787) (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term76 _25786 _25787 h _18046.
Proof. exact (fun f : type1470 _25786 _25787 => @lem1109299 _25786 _25787 h f _18046 h1). Qed.
Lemma lem1109301 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term88 _25786 _25787 _18046) : term80 _25786 _25787 _18046.
Proof. exact (fun h : _25787 => @lem1109300 _25786 _25787 h _18046 h1). Qed.
Lemma lem1109302 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term99 _25786 _25787 _18046.
Proof. exact (h1). Qed.
Lemma lem1109303 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term88 _25786 _25787 _18046.
Proof. exact (proj2 (@lem1109302 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109304 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : (_18046 (@nil _25787)) = (term83 _25786 _25787).
Proof. exact (proj1 (@lem1109302 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109305 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : ((_18046 (@nil _25787)) = (term83 _25786 _25787)) = (term36 _25786 _25787 _18046).
Proof. exact (prop_ext (fun h2 : (_18046 (@nil _25787)) = (term83 _25786 _25787) => @lem1109278 _25786 _25787 _18046 h2) (fun h2 : term36 _25786 _25787 _18046 => @lem1109304 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109306 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term36 _25786 _25787 _18046.
Proof. exact (EQ_MP (@lem1109305 _25786 _25787 _18046 h1) (@lem1109304 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109307 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : (term88 _25786 _25787 _18046) = (term80 _25786 _25787 _18046).
Proof. exact (prop_ext (fun h2 : term88 _25786 _25787 _18046 => @lem1109301 _25786 _25787 _18046 h2) (fun h2 : term80 _25786 _25787 _18046 => @lem1109303 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109308 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term80 _25786 _25787 _18046.
Proof. exact (EQ_MP (@lem1109307 _25786 _25787 _18046 h1) (@lem1109303 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109309 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term82 _25786 _25787 _18046.
Proof. exact (conj (@lem1109306 _25786 _25787 _18046 h1) (@lem1109308 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109310 {A Z : Type'} (NIL' : Z) : term100 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1109311 {A Z : Type'} (NIL' : Z) : (term100 A Z NIL') = (term101 A Z NIL').
Proof. exact (eq_refl (term100 A Z NIL')). Qed.
Lemma lem1109312 {A Z : Type'} (NIL' : Z) : term101 A Z NIL'.
Proof. exact (EQ_MP (@lem1109311 A Z NIL') (@lem1109310 A Z NIL')). Qed.
Lemma lem1109313 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term102 A Z NIL' CONS'.
Proof. exact (@lem1109312 A Z NIL' CONS'). Qed.
Lemma lem1109314 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term102 A Z NIL' CONS') = (term103 A Z NIL' CONS').
Proof. exact (eq_refl (term102 A Z NIL' CONS')). Qed.
Lemma lem1109315 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term103 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1109314 A Z NIL' CONS') (@lem1109313 A Z NIL' CONS')). Qed.
Lemma lem1109316 {_25786 _25787 : Type'} (NIL' : type735 _25786 _25787) (CONS' : type1459 _25786 _25787) : term104 _25786 _25787 NIL' CONS'.
Proof. exact (@lem1109315 _25787 (type735 _25786 _25787) NIL' CONS'). Qed.
Lemma lem1109317 {_25786 _25787 : Type'} : term105 _25786 _25787.
Proof. exact (@lem1109316 _25786 _25787 (term83 _25786 _25787) (term106 _25786 _25787)). Qed.
Lemma lem1109318 {_25786 _25787 : Type'} (a0 : _25787) : (term107 _25786 _25787 a0) = (term108 _25786 _25787 a0).
Proof. exact (eq_refl (term107 _25786 _25787 a0)). Qed.
Lemma lem1109319 {_25787 : Type'} (a1 : list _25787) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1109320 {_25786 _25787 : Type'} (a0 : _25787) (a1 : list _25787) : (term109 _25786 _25787 a0 a1) = (term110 _25786 _25787 a0 a1).
Proof. exact (MK_COMB (@lem1109318 _25786 _25787 a0) (@lem1109319 _25787 a1)). Qed.
Lemma lem1109321 {_25786 _25787 : Type'} (a1 : list _25787) (a0 : _25787) : (term110 _25786 _25787 a0 a1) = (term111 _25786 _25787 a0).
Proof. exact (eq_refl (term110 _25786 _25787 a0 a1)). Qed.
Lemma lem1109322 {_25786 _25787 : Type'} (a1 : list _25787) (a0 : _25787) : (term109 _25786 _25787 a0 a1) = (term111 _25786 _25787 a0).
Proof. exact (TRANS (@lem1109320 _25786 _25787 a0 a1) (@lem1109321 _25786 _25787 a1 a0)). Qed.
Lemma lem1109323 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) (a1 : list _25787) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1109324 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) (a1 : list _25787) : (term112 _25786 _25787 a0 fn a1) = (term113 _25786 _25787 a0 fn a1).
Proof. exact (MK_COMB (@lem1109322 _25786 _25787 a1 a0) (@lem1109323 _25786 _25787 fn a1)). Qed.
Lemma lem1109325 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) (a1 : list _25787) : (term113 _25786 _25787 a0 fn a1) = (term93 _25786 _25787 a0 fn a1).
Proof. exact (eq_refl (term113 _25786 _25787 a0 fn a1)). Qed.
Lemma lem1109326 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) (a1 : list _25787) : (term112 _25786 _25787 a0 fn a1) = (term93 _25786 _25787 a0 fn a1).
Proof. exact (TRANS (@lem1109324 _25786 _25787 a0 fn a1) (@lem1109325 _25786 _25787 a0 fn a1)). Qed.
Lemma lem1109327 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) (a0 : _25787) (a1 : list _25787) : (term114 _25786 _25787 fn a0 a1) = (term114 _25786 _25787 fn a0 a1).
Proof. exact (eq_refl (term114 _25786 _25787 fn a0 a1)). Qed.
Lemma lem1109328 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) (a1 : list _25787) : ((term92 _25786 _25787 fn a0 a1) = (term112 _25786 _25787 a0 fn a1)) = ((term92 _25786 _25787 fn a0 a1) = (term93 _25786 _25787 a0 fn a1)).
Proof. exact (MK_COMB (@lem1109327 _25786 _25787 fn a0 a1) (@lem1109326 _25786 _25787 a0 fn a1)). Qed.
Lemma lem1109329 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) : (term115 _25786 _25787 a0 fn) = (term116 _25786 _25787 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25787 => @lem1109328 _25786 _25787 a0 fn a1)). Qed.
Lemma lem1109330 {_25787 : Type'} : (@all (list _25787)) = (@all (list _25787)).
Proof. exact (eq_refl (@all (list _25787))). Qed.
Lemma lem1109331 {_25786 _25787 : Type'} (a0 : _25787) (fn : type1146 _25786 _25787) : (term117 _25786 _25787 a0 fn) = (term90 _25786 _25787 a0 fn).
Proof. exact (MK_COMB (@lem1109330 _25787) (@lem1109329 _25786 _25787 a0 fn)). Qed.
Lemma lem1109332 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) : (term118 _25786 _25787 fn) = (term119 _25786 _25787 fn).
Proof. exact (fun_ext (fun a0 : _25787 => @lem1109331 _25786 _25787 a0 fn)). Qed.
Lemma lem1109333 {_25787 : Type'} : (@all _25787) = (@all _25787).
Proof. exact (eq_refl (@all _25787)). Qed.
Lemma lem1109334 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) : (term120 _25786 _25787 fn) = (term88 _25786 _25787 fn).
Proof. exact (MK_COMB (@lem1109333 _25787) (@lem1109332 _25786 _25787 fn)). Qed.
Lemma lem1109335 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) : (term121 _25786 _25787 fn) = (term121 _25786 _25787 fn).
Proof. exact (eq_refl (term121 _25786 _25787 fn)). Qed.
Lemma lem1109336 {_25786 _25787 : Type'} (fn : type1146 _25786 _25787) : (term122 _25786 _25787 fn) = (term99 _25786 _25787 fn).
Proof. exact (MK_COMB (@lem1109335 _25786 _25787 fn) (@lem1109334 _25786 _25787 fn)). Qed.
Lemma lem1109337 {_25786 _25787 : Type'} : (term123 _25786 _25787) = (term124 _25786 _25787).
Proof. exact (fun_ext (fun fn : type1146 _25786 _25787 => @lem1109336 _25786 _25787 fn)). Qed.
Lemma lem1109338 {_25786 _25787 : Type'} : (@ex ((list _25787) -> (_25787 -> _25786 -> Prop) -> (list _25786) -> Prop)) = (@ex ((list _25787) -> (_25787 -> _25786 -> Prop) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25787) -> (_25787 -> _25786 -> Prop) -> (list _25786) -> Prop))). Qed.
Lemma lem1109339 {_25786 _25787 : Type'} : (term105 _25786 _25787) = (term125 _25786 _25787).
Proof. exact (MK_COMB (@lem1109338 _25786 _25787) (@lem1109337 _25786 _25787)). Qed.
Lemma lem1109340 {_25786 _25787 : Type'} : term125 _25786 _25787.
Proof. exact (EQ_MP (@lem1109339 _25786 _25787) (@lem1109317 _25786 _25787)). Qed.
Lemma lem1109341 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term99 _25786 _25787 _18046.
Proof. exact (h1). Qed.
Lemma lem1109342 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term88 _25786 _25787 _18046.
Proof. exact (proj2 (@lem1109341 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109343 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : (_18046 (@nil _25787)) = (term83 _25786 _25787).
Proof. exact (proj1 (@lem1109341 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109344 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term99 _25786 _25787 _18046.
Proof. exact (conj (@lem1109343 _25786 _25787 _18046 h1) (@lem1109342 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109345 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term125 _25786 _25787.
Proof. exact (ex_intro (term124 _25786 _25787) _18046 (@lem1109344 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109346 {_25786 _25787 : Type'} (h1 : term125 _25786 _25787) : term125 _25786 _25787.
Proof. exact (h1). Qed.
Lemma lem1109347 {_25786 _25787 : Type'} (h1 : term125 _25786 _25787) : term125 _25786 _25787.
Proof. exact (ex_elim (@lem1109346 _25786 _25787 h1) (fun _18046 : type1146 _25786 _25787 => fun h0 : term124 _25786 _25787 _18046 => @lem1109345 _25786 _25787 _18046 h0)). Qed.
Lemma lem1109348 {_25786 _25787 : Type'} : (term125 _25786 _25787) = (term125 _25786 _25787).
Proof. exact (prop_ext (fun h1 : term125 _25786 _25787 => @lem1109347 _25786 _25787 h1) (fun h1 : term125 _25786 _25787 => @lem1109340 _25786 _25787)). Qed.
Lemma lem1109349 {_25786 _25787 : Type'} : term125 _25786 _25787.
Proof. exact (EQ_MP (@lem1109348 _25786 _25787) (@lem1109340 _25786 _25787)). Qed.
Lemma lem1109350 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term99 _25786 _25787 _18046) : term126 _25786 _25787.
Proof. exact (ex_intro (term127 _25786 _25787) _18046 (@lem1109309 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109351 {_25786 _25787 : Type'} (h1 : term125 _25786 _25787) : term125 _25786 _25787.
Proof. exact (h1). Qed.
Lemma lem1109352 {_25786 _25787 : Type'} (h1 : term125 _25786 _25787) : term126 _25786 _25787.
Proof. exact (ex_elim (@lem1109351 _25786 _25787 h1) (fun _18046 : type1146 _25786 _25787 => fun h0 : term124 _25786 _25787 _18046 => @lem1109350 _25786 _25787 _18046 h0)). Qed.
Lemma lem1109353 {_25786 _25787 : Type'} : (term125 _25786 _25787) = (term126 _25786 _25787).
Proof. exact (prop_ext (fun h1 : term125 _25786 _25787 => @lem1109352 _25786 _25787 h1) (fun h1 : term126 _25786 _25787 => @lem1109349 _25786 _25787)). Qed.
Lemma lem1109354 {_25786 _25787 : Type'} : term126 _25786 _25787.
Proof. exact (EQ_MP (@lem1109353 _25786 _25787) (@lem1109349 _25786 _25787)). Qed.
Lemma lem1109355 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) : term82 _25786 _25787 _18046.
Proof. exact (h1). Qed.
Lemma lem1109356 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : (term82 _25786 _25787 _18046) = (term81 _25786 _25787 ALLPAIRS').
Proof. exact (SYM (@lem1109263 _25786 _25787 ALLPAIRS' _18046 h1)). Qed.
Lemma lem1109357 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) (h2 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : term81 _25786 _25787 ALLPAIRS'.
Proof. exact (EQ_MP (@lem1109356 _25786 _25787 ALLPAIRS' _18046 h2) (@lem1109355 _25786 _25787 _18046 h1)). Qed.
Lemma lem1109358 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) (h2 : ALLPAIRS' = (term4 _25786 _25787 _18046)) : term128 _25786 _25787.
Proof. exact (ex_intro (term129 _25786 _25787) ALLPAIRS' (@lem1109357 _25786 _25787 ALLPAIRS' _18046 h1 h2)). Qed.
Lemma lem1109359 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) : (term4 _25786 _25787 _18046) = (term4 _25786 _25787 _18046).
Proof. exact (eq_refl (term4 _25786 _25787 _18046)). Qed.
Lemma lem1109360 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) : term130 _25786 _25787 ALLPAIRS' _18046.
Proof. exact (fun h0 : ALLPAIRS' = (term4 _25786 _25787 _18046) => @lem1109358 _25786 _25787 ALLPAIRS' _18046 h1 h0). Qed.
Lemma lem1109361 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) : term131 _25786 _25787 _18046.
Proof. exact (@lem1109360 _25786 _25787 (term4 _25786 _25787 _18046) _18046 h1). Qed.
Lemma lem1109362 {_25786 _25787 : Type'} (_18046 : type1146 _25786 _25787) (h1 : term82 _25786 _25787 _18046) : term128 _25786 _25787.
Proof. exact (@lem1109361 _25786 _25787 _18046 h1 (@lem1109359 _25786 _25787 _18046)). Qed.
Lemma lem1109363 {_25786 _25787 : Type'} (h1 : term126 _25786 _25787) : term126 _25786 _25787.
Proof. exact (h1). Qed.
Lemma lem1109364 {_25786 _25787 : Type'} (h1 : term126 _25786 _25787) : term128 _25786 _25787.
Proof. exact (ex_elim (@lem1109363 _25786 _25787 h1) (fun _18046 : type1146 _25786 _25787 => fun h0 : term127 _25786 _25787 _18046 => @lem1109362 _25786 _25787 _18046 h0)). Qed.
Lemma lem1109365 {_25786 _25787 : Type'} : (term126 _25786 _25787) = (term128 _25786 _25787).
Proof. exact (prop_ext (fun h1 : term126 _25786 _25787 => @lem1109364 _25786 _25787 h1) (fun h1 : term128 _25786 _25787 => @lem1109354 _25786 _25787)). Qed.
Lemma lem1109366 {_25786 _25787 : Type'} : term128 _25786 _25787.
Proof. exact (EQ_MP (@lem1109365 _25786 _25787) (@lem1109354 _25786 _25787)). Qed.
Lemma lem1109367 {_25786 _25787 : Type'} : term132 _25786 _25787.
Proof. exact (fun _18050 : type1669 => @lem1109366 _25786 _25787). Qed.
Lemma lem1109368 {A B : Type'} (P : type1413 A B) : term133 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1109369 {A B : Type'} (P : type1413 A B) : (term133 A B P) = ((term134 A B P) = (term135 A B P)).
Proof. exact (eq_refl (term133 A B P)). Qed.
Lemma lem1109372 {A B : Type'} (P : type1413 A B) : (term134 A B P) = (term135 A B P).
Proof. exact (EQ_MP (@lem1109369 A B P) (@lem1109368 A B P)). Qed.
Lemma lem1109373 {_25786 _25787 : Type'} (P : type1242 _25786 _25787) : (term136 _25786 _25787 P) = (term137 _25786 _25787 P).
Proof. exact (@lem1109372 type1669 (type736 _25786 _25787) P). Qed.
Lemma lem1109374 {_25786 _25787 : Type'} : (term138 _25786 _25787) = (term139 _25786 _25787).
Proof. exact (@lem1109373 _25786 _25787 (term140 _25786 _25787)). Qed.
Lemma lem1109375 {_25786 _25787 : Type'} (_18050 : type1669) : (term141 _25786 _25787 _18050) = (term129 _25786 _25787).
Proof. exact (eq_refl (term141 _25786 _25787 _18050)). Qed.
Lemma lem1109376 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) : ALLPAIRS' = ALLPAIRS'.
Proof. exact (eq_refl ALLPAIRS'). Qed.
Lemma lem1109377 {_25786 _25787 : Type'} (_18050 : type1669) (ALLPAIRS' : type736 _25786 _25787) : (term142 _25786 _25787 _18050 ALLPAIRS') = (term143 _25786 _25787 ALLPAIRS').
Proof. exact (MK_COMB (@lem1109375 _25786 _25787 _18050) (@lem1109376 _25786 _25787 ALLPAIRS')). Qed.
Lemma lem1109378 {_25786 _25787 : Type'} (ALLPAIRS' : type736 _25786 _25787) : (term143 _25786 _25787 ALLPAIRS') = (term81 _25786 _25787 ALLPAIRS').
Proof. exact (eq_refl (term143 _25786 _25787 ALLPAIRS')). Qed.
Lemma lem1109379 {_25786 _25787 : Type'} (_18050 : type1669) (ALLPAIRS' : type736 _25786 _25787) : (term142 _25786 _25787 _18050 ALLPAIRS') = (term81 _25786 _25787 ALLPAIRS').
Proof. exact (TRANS (@lem1109377 _25786 _25787 _18050 ALLPAIRS') (@lem1109378 _25786 _25787 ALLPAIRS')). Qed.
Lemma lem1109380 {_25786 _25787 : Type'} (_18050 : type1669) : (term144 _25786 _25787 _18050) = (term129 _25786 _25787).
Proof. exact (fun_ext (fun ALLPAIRS' : type736 _25786 _25787 => @lem1109379 _25786 _25787 _18050 ALLPAIRS')). Qed.
Lemma lem1109381 {_25786 _25787 : Type'} : (@ex ((_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop)) = (@ex ((_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@ex ((_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop))). Qed.
Lemma lem1109382 {_25786 _25787 : Type'} (_18050 : type1669) : (term145 _25786 _25787 _18050) = (term128 _25786 _25787).
Proof. exact (MK_COMB (@lem1109381 _25786 _25787) (@lem1109380 _25786 _25787 _18050)). Qed.
Lemma lem1109383 {_25786 _25787 : Type'} : (term146 _25786 _25787) = (term147 _25786 _25787).
Proof. exact (fun_ext (fun _18050 : type1669 => @lem1109382 _25786 _25787 _18050)). Qed.
Lemma lem1109384 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1109385 {_25786 _25787 : Type'} : (term138 _25786 _25787) = (term132 _25786 _25787).
Proof. exact (MK_COMB (@lem1109384) (@lem1109383 _25786 _25787)). Qed.
Lemma lem1109386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109387 {_25786 _25787 : Type'} : (term148 _25786 _25787) = (term149 _25786 _25787).
Proof. exact (MK_COMB (@lem1109386) (@lem1109385 _25786 _25787)). Qed.
Lemma lem1109388 {_25786 _25787 : Type'} (_18050 : type1669) : (term141 _25786 _25787 _18050) = (term129 _25786 _25787).
Proof. exact (eq_refl (term141 _25786 _25787 _18050)). Qed.
Lemma lem1109389 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) (_18050 : type1669) : (ALLPAIRS' _18050) = (ALLPAIRS' _18050).
Proof. exact (eq_refl (ALLPAIRS' _18050)). Qed.
Lemma lem1109390 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) (_18050 : type1669) : (term150 _25786 _25787 ALLPAIRS' _18050) = (term151 _25786 _25787 ALLPAIRS' _18050).
Proof. exact (MK_COMB (@lem1109388 _25786 _25787 _18050) (@lem1109389 _25786 _25787 ALLPAIRS' _18050)). Qed.
Lemma lem1109391 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) (_18050 : type1669) : (term151 _25786 _25787 ALLPAIRS' _18050) = (term152 _25786 _25787 ALLPAIRS' _18050).
Proof. exact (eq_refl (term151 _25786 _25787 ALLPAIRS' _18050)). Qed.
Lemma lem1109392 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) (_18050 : type1669) : (term150 _25786 _25787 ALLPAIRS' _18050) = (term152 _25786 _25787 ALLPAIRS' _18050).
Proof. exact (TRANS (@lem1109390 _25786 _25787 ALLPAIRS' _18050) (@lem1109391 _25786 _25787 ALLPAIRS' _18050)). Qed.
Lemma lem1109393 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) : (term153 _25786 _25787 ALLPAIRS') = (term154 _25786 _25787 ALLPAIRS').
Proof. exact (fun_ext (fun _18050 : type1669 => @lem1109392 _25786 _25787 ALLPAIRS' _18050)). Qed.
Lemma lem1109394 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1109395 {_25786 _25787 : Type'} (ALLPAIRS' : type1245 _25786 _25787) : (term155 _25786 _25787 ALLPAIRS') = (term156 _25786 _25787 ALLPAIRS').
Proof. exact (MK_COMB (@lem1109394) (@lem1109393 _25786 _25787 ALLPAIRS')). Qed.
Lemma lem1109396 {_25786 _25787 : Type'} : (term157 _25786 _25787) = (term158 _25786 _25787).
Proof. exact (fun_ext (fun ALLPAIRS' : type1245 _25786 _25787 => @lem1109395 _25786 _25787 ALLPAIRS')). Qed.
Lemma lem1109397 {_25786 _25787 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop))). Qed.
Lemma lem1109398 {_25786 _25787 : Type'} : (term139 _25786 _25787) = (term159 _25786 _25787).
Proof. exact (MK_COMB (@lem1109397 _25786 _25787) (@lem1109396 _25786 _25787)). Qed.
Lemma lem1109399 {_25786 _25787 : Type'} : ((term138 _25786 _25787) = (term139 _25786 _25787)) = ((term132 _25786 _25787) = (term159 _25786 _25787)).
Proof. exact (MK_COMB (@lem1109387 _25786 _25787) (@lem1109398 _25786 _25787)). Qed.
Lemma lem1109400 {_25786 _25787 : Type'} : (term132 _25786 _25787) = (term159 _25786 _25787).
Proof. exact (EQ_MP (@lem1109399 _25786 _25787) (@lem1109374 _25786 _25787)). Qed.
Lemma lem1109401 {_25786 _25787 : Type'} : term159 _25786 _25787.
Proof. exact (EQ_MP (@lem1109400 _25786 _25787) (@lem1109367 _25786 _25787)). Qed.
Lemma lem1109403 {A : Type'} : (@ex A) = (term160 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1109404 {_25786 _25787 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (_25787 -> _25786 -> Prop) -> (list _25787) -> (list _25786) -> Prop)) = (term161 _25786 _25787).
Proof. exact (@lem1109403 (type1245 _25786 _25787)). Qed.
Lemma lem1109405 {_25786 _25787 : Type'} : (term158 _25786 _25787) = (term158 _25786 _25787).
Proof. exact (eq_refl (term158 _25786 _25787)). Qed.
Lemma lem1109406 {_25786 _25787 : Type'} : (term159 _25786 _25787) = (term162 _25786 _25787).
Proof. exact (MK_COMB (@lem1109404 _25786 _25787) (@lem1109405 _25786 _25787)). Qed.
Lemma lem1109407 {_25786 _25787 : Type'} : (term162 _25786 _25787) = (term163 _25786 _25787).
Proof. exact (eq_refl (term162 _25786 _25787)). Qed.
Lemma lem1109408 {_25786 _25787 : Type'} : (term159 _25786 _25787) = (term163 _25786 _25787).
Proof. exact (TRANS (@lem1109406 _25786 _25787) (@lem1109407 _25786 _25787)). Qed.
Lemma lem1109409 {_25786 _25787 : Type'} : term163 _25786 _25787.
Proof. exact (EQ_MP (@lem1109408 _25786 _25787) (@lem1109401 _25786 _25787)). Qed.
