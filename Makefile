ARCHIVE_DIR=VPrl


domain_th.vo : cequiv.vo sqle.vo domain_th.v
	coqc domain_th.v

cequiv.vo : approx_star.vo cequiv.v
	coqc cequiv.v

cequiv2.vo : cequiv2.v cequiv.vo
	coqc cequiv2.v

cequiv_tacs.vo : cequiv_tacs.v cequiv2.vo
	coqc cequiv_tacs.v

approx_star.vo : approx.vo approx_star.v
	coqc approx_star.v

approx.vo : approx.v computation3.vo bin_rels.vo rel_nterm.vo
	coqc approx.v

rel_nterm.vo : rel_nterm.v alphaeq.vo
	coqc rel_nterm.v

alphaeq.vo : alphaeq.v substitution.vo
	coqc alphaeq.v

substitution.vo : substitution.v terms2.vo lmap.vo
	coqc substitution.v

subst_tacs.vo : subst_tacs.v csubst.vo
	coqc subst_tacs.v

sqle.vo : approx.vo sqle.v bin_rels.vo
	coqc sqle.v

squiggle.vo : squiggle.v computation3.vo bin_rels.vo
	coqc squiggle.v


computation1.vo : substitution.vo computation1.v
	coqc computation1.v

computation.vo : computation1.vo substitution.vo computation.v
	coqc computation.v

computation3.vo : computation.vo  alphaeq.vo rel_nterm.vo computation3.v
	coqc computation3.v

terms.vo : terms.v variables.vo opid.vo
	coqc terms.v

terms2.vo : terms2.v terms.vo
	coqc terms2.v

terms_per.vo : terms_per.v terms2.vo tactics2.vo
	coqc terms_per.v

subst_per.vo : subst_per.v csubst.vo terms_per.vo
	coqc subst_per.v

opid.vo : opid.v list.vo
	coqc opid.v

variables.vo : variables.v list.vo
	coqc variables.v

UsefulTypes.vo : UsefulTypes.v tactics.vo
	coqc UsefulTypes.v

list.vo : list.v UsefulTypes.vo bin_rels.vo
	coqc list.v

tactics.vo : tactics.v eq_rel.vo LibTactics.vo
	coqc tactics.v

bin_rels.vo : bin_rels.v UsefulTypes.vo
	coqc bin_rels.v

eq_rel.vo : eq_rel.v universe.vo
	coqc eq_rel.v

axioms.vo : axioms.v
	coqc axioms.v

lmap.vo : lmap.v list.vo
	coqc lmap.v

LibTactics.vo : LibTactics.v
	coqc LibTactics.v

universe2.vo : universe2.v
	coqc universe.v

per.vo : per.v cequiv.vo universe2.vo cequiv2.vo
	coqc universe2.v
	coqc per.v

choice.vo : choice.v nuprl_props.vo
	coqc choice.v

per_props.vo : per_props.v nuprl_props.vo choice.vo
	coqc per_props.v

per_props2.vo : per_props2.v per_props.vo subst_per.vo cequiv_tacs.vo sequents_tacs.vo subst_tacs.vo
	coqc per_props2.v

per_props_per.vo : per_props_per.v per_props2.vo rwper.vo subst_tacs.vo cequiv_tacs.vo
	coqc per_props_per.v

nuprl_props.vo : nuprl_props.v nuprl_type_sys.vo univ_tacs.vo
	coqc nuprl_props.v

univ_tacs.vo : univ_tacs.v nuprl.vo type_sys.vo
	coqc univ_tacs.v

nuprl.vo : nuprl.v per.vo
	coqc nuprl.v

universe2_type.vo : universe2_type.v cequiv.vo
	coqc universe2_type.v

nuprl_fin.vo : nuprl_fin.v cequiv.vo universe2_type.vo
	coqc nuprl_fin.v

type_sys.vo : type_sys.v nuprl.vo
	coqc type_sys.v

type_sys_pfam.vo : type_sys_pfam.v type_sys_useful2.vo tactics2.vo
	coqc type_sys_pfam.v


dest_close.vo : dest_close.v type_sys.vo
	coqc dest_close.v

close_type_sys_constructors = close_type_sys_per_int.vo \
                    close_type_sys_per_base.vo \
                    close_type_sys_per_sqle.vo \
                    close_type_sys_per_sqequal.vo \
                    close_type_sys_per_init.vo \
                    close_type_sys_per_eq.vo \
                    close_type_sys_per_teq.vo \
                    close_type_sys_per_isect.vo \
                    close_type_sys_per_func.vo \
                    close_type_sys_per_disect.vo \
                    close_type_sys_per_pertype.vo \
                    close_type_sys_per_ipertype.vo \
                    close_type_sys_per_spertype.vo \
                    close_type_sys_per_w.vo \
                    close_type_sys_per_pw.vo \
                    close_type_sys_per_pm.vo \
                    close_type_sys_per_m.vo \
                    close_type_sys_per_union.vo \
                    close_type_sys_per_image.vo \
                    close_type_sys_per_partial.vo \
                    close_type_sys_per_admiss.vo \
                    close_type_sys_per_mono.vo \
                    close_type_sys_per_set.vo \
                    close_type_sys_per_product.vo

$(close_type_sys_constructors): %.vo: %.v type_sys.vo type_sys_useful.vo dest_close.vo type_sys_pfam.vo pweq_lemmas.vo pmeq_lemmas.vo
	coqc $<


close_type_sys.vo : close_type_sys.v \
                    type_sys.vo \
		    $(close_type_sys_constructors) \
                    type_sys_useful2.vo
	coqc close_type_sys.v

type_sys_useful.vo : type_sys_useful.v type_sys.vo
	coqc type_sys_useful.v

type_sys_useful2.vo : type_sys_useful2.v type_sys_useful.vo
	coqc type_sys_useful2.v

pweq_lemmas.vo : pweq_lemmas.v type_sys_pfam.vo
	coqc pweq_lemmas.v

pmeq_lemmas.vo : pmeq_lemmas.v type_sys_pfam.vo
	coqc pmeq_lemmas.v

nuprl_type_sys.vo : nuprl_type_sys.v close_type_sys.vo
	coqc nuprl_type_sys.v

per_props_more.vo : per_props_more.v per_props.vo
	coqc per_props_more.v

lift_lsubst_tacs.vo : lift_lsubst_tacs.v csubst.vo cequiv2.vo subst_per.vo
	coqc lift_lsubst_tacs.v

csubst.vo : csubst.v alphaeq.vo
	coqc csubst.v

sequents.vo : sequents.v per_props_more.vo csubst.vo
	coqc sequents.v

sequents_tacs.vo : sequents_tacs.v sequents.vo lift_lsubst_tacs.vo
	coqc sequents_tacs.v

sequents_useful.vo : sequents_useful.v sequents_tacs.vo
	coqc sequents_useful.v

rules_function.vo : rules_function.v rules_useful.vo subst_tacs.vo cequiv_tacs.vo
	coqc rules_function.v

rules_partial.vo : rules_partial.v sequents_tacs.vo rules_useful.vo domain_th.vo
	coqc rules_partial.v

rules_mono.vo : rules_partial.vo rules_mono.v
	coqc rules_mono.v

rules_admiss.vo : rules_mono.vo rules_admiss.v
	coqc rules_admiss.v

rules_struct.vo : rules_struct.v rules_useful.vo sequents_useful.vo
	coqc rules_struct.v

tactics2.vo : tactics2.v eq_rel.vo tactics.vo substitution.vo
	coqc tactics2.v

nuprl_lemmas2.vo : nuprl_lemmas2.v sequents_tacs.vo rules_isect.vo rules_squiggle.vo rules_struct.vo tactics2.vo
	coqc nuprl_lemmas2.v

rules_pertype.vo : rules_pertype.v sequents_tacs.vo sequents_useful.vo
	coqc rules_pertype.v

rules_pertype2.vo : rules_pertype2.v rules_pertype.vo subst_per.vo tactics2.vo cequiv_tacs.vo subst_tacs.vo per_props2.vo
	coqc rules_pertype2.v

rules_ipertype.vo : rules_ipertype.v sequents_tacs.vo sequents_useful.vo
	coqc rules_ipertype.v

rules_spertype.vo : rules_spertype.v sequents_tacs.vo sequents_useful.vo
	coqc rules_spertype.v

rules_tequality.vo : rules_tequality.v sequents_tacs.vo per_props2.vo subst_tacs.vo
	coqc rules_tequality.v

rwper.vo : rwper.v per_props2.vo
	coqc rwper.v

rules_per_function.vo : rules_per_function.v sequents_tacs.vo rules_pertype2.vo subst_tacs.vo cequiv_tacs.vo tactics2.vo per_props_per.vo rwper.vo
	coqc rules_per_function.v

rules_iper_function.vo : rules_iper_function.v sequents_tacs.vo rules_pertype2.vo subst_tacs.vo cequiv_tacs.vo tactics2.vo per_props_per.vo rwper.vo
	coqc rules_iper_function.v

rules_isect.vo : rules_isect.v sequents_tacs.vo sequents_useful.vo
	coqc rules_isect.v

rules_isect2.vo : rules_isect2.v sequents_tacs.vo
	coqc rules_isect2.v

rules_squiggle.vo : rules_squiggle.v sequents_tacs.vo sequents_useful.vo
	coqc rules_squiggle.v

rules_squiggle2.vo : rules_squiggle2.v rules_useful.vo sequents_useful.vo
	coqc rules_squiggle2.v

rules_classical.vo : rules_classical.v sequents_tacs.vo sequents_useful.vo
	coqc rules_classical.v

rules_cft.vo : rules_cft.v sequents_tacs.vo cequiv2.vo subst_tacs.vo
	coqc rules_cft.v

rules_hasvalue.vo : rules_hasvalue.v sequents_tacs.vo
	coqc rules_hasvalue.v

rules_useful.vo : rules_useful.v sequents_tacs.vo sequents_useful.vo
	coqc rules_useful.v

rules_w.vo : rules_w.v rules_useful.vo sequents_useful.vo
	coqc rules_w.v

rules_pw_useful.vo : rules_pw_useful.v rules_useful.vo sequents_useful.vo
	coqc rules_pw_useful.v

rules_pw3.vo : rules_pw3.v rules_pw_useful.vo pweq_lemmas.vo 
	coqc rules_pw3.v

universe.vo : universe.v
	coqc universe.v


type_system_intro.vo : type_system_intro.v cequiv.vo
	coqc type_system_intro.v



rules_paper: rules_function.vo \
	     rules_pertype.vo \
	     rules_ipertype.vo \
	     rules_spertype.vo \
	     rules_tequality.vo \
	     rules_partial.vo \
	     rules_w.vo \
	     rules_pw3.vo \
             rules_partial.vo \
             rules_isect.vo \
             rules_isect2.vo \
             rules_squiggle.vo \
             rules_squiggle2.vo \
             rules_classical.vo \
             rules_cft.vo \
             rules_hasvalue.vo \
             rules_iper_function.vo \
             rules_struct.vo

clean : clean_raw
	rm -f *.glob *.vo *.cmi *.cmx *.cmxs *.native doc/coqdoc/*.aux doc/coqdoc/*.tex doc/coqdoc/html/*.html doc/verification.pdf


proviola = variables \
	  substitution \
	  approx_star \
	  domain_th \
	  rules_partial

coqdocs = variables \
	  eq_rel \
	  universe \
	  UsefulTypes \
	  list \
	  sqle \
	  terms \
	  terms2 \
	  substitution \
	  alphaeq \
	  computation \
	  computation1 \
	  computation3 \
	  approx \
	  approx_star \
	  cequiv \
	  domain_th \
	  type_system_intro \
	  per \
	  opid \
	  nuprl \
	  type_sys \
	  close_type_sys \
	  nuprl_type_sys \
	  per_props \
	  sequents \
	  rules_function \
	  rules_struct \
	  rules_squiggle \
	  rules_squiggle2 \
	  rules_classical \
	  rules_cft \
	  rules_hasvalue \
	  rules_iper_function \
	  rules_pertype \
	  rules_ipertype \
	  rules_spertype \
	  rules_tequality \
	  rules_partial \
	  rules_mono \
	  rules_admiss \
	  rules_isect \
	  rules_isect2 \
	  rules_w \
	  rel_nterm \
	  nuprl_lemmas2 \
	  nuprl_fin \
	  rules_pw3

%.vo : %.v
	coqc $< 

V_FILES := $(wildcard *.v)
coqdocstex = $(coqdocs:=.tex)
coqdocstexpath = $(addprefix doc/coqdoc/, $(coqdocstex))
V_FILES_RAW = $(addprefix doc/rawv/, $(V_FILES))
coqdocsvo = $(coqdocs:=.vo)
coqdocshtml = $(coqdocs:=.html)
coqdocsrawhtm = $(coqdocs:=.htm)
coqdocsrawflm = $(coqdocs:=.flm)
coqdocsrawhtml = $(addprefix doc/rawv/, $(coqdocshtml))
doc/coqdoc/%.tex: %.v
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)
doc/rawv/%.v: %.v
	# cat remove_printing.v > $(@)
	grep -vwE "((begin|end) hide)|(\*\* printing)" $< >> $(@)
	#grep -vwE "((begin|end) hide)" $< >> $(@)
everything.vo : coqdoc-outputs-vo
	coqc everything.v

archive:
	# Re-creating archive directory
	rm -rf ${ARCHIVE_DIR}
	mkdir ${ARCHIVE_DIR}
	# Copying necessary files
	cp ${V_FILES} ${ARCHIVE_DIR}
	cp Makefile ${ARCHIVE_DIR}
	cp LICENCE ${ARCHIVE_DIR}
	cp README ${ARCHIVE_DIR}
	# Making archive
	tar -cvzf ${ARCHIVE_DIR}.tar.gz ${ARCHIVE_DIR}
	rm -rf ${ARCHIVE_DIR}

#doc/rawv/%.html: doc/rawv/%.v
#	coqdoc  --interpolate $< -o $(@) --no-index
#	camera.py $(@) temp
#	xsltproc temp > $(@)

coqdoc-outputs-vo : $(coqdocsvo)
coqdoc-outputs :  $(coqdocstexpath)

pdf : coqdoc-outputs-vo coqdoc-outputs doc/verification.tex
	(cd doc; rubber -ps -d verification)

%.html: %.v
	coqdoc  --interpolate $< -o $(@) --no-index -utf8

#%.htm: %.html
#	camera.py $< temp
#	xsltproc temp > $(@)

coqdocs-htmls : $(coqdocshtml)
	#cp coqdoc.css doc/coqdoc/html

%.flm: %.v
	camera.py $< $(@)

%.htm: %.flm
	xsltproc $< > $(@)


coqdoc-htms : $(coqdocsrawhtm)

proviola :
	make -f Makefile  -C doc/rawv coqdoc-htms -j3

website : website-htmls website-raw-htmls website-pdf

clean_raw :
	rm -f doc/rawv/*.v
	rm -f doc/rawv/*.vo
	rm -f doc/rawv/*.glob
	rm -f doc/rawv/*.htm
	rm -f doc/rawv/*.html
	rm -f doc/rawv/*.flm
	rm -f doc/rawv/*.xml
	rm -f doc/coqdoc/rawhtmls/*
	rm -f temp


website-htmls:
	mv *.html doc/coqdoc/html/
	scp -r doc/coqdoc/html/ npweb:/var/www/html/html/verification/v1/
website-raw-htmls:
	mv doc/rawv/*.html doc/coqdoc/rawhtmls/
	cp doc/rawv/coqdoc.css doc/coqdoc/rawhtmls/
	scp -r doc/coqdoc/rawhtmls/*  npweb:/var/www/html/html/verification/v1/html/raw/
website-pdf: doc/verification.pdf
	scp doc/verification.pdf npweb:/var/www/html/html/verification/


website-archive: archive
	scp ${ARCHIVE_DIR}.tar.gz npweb:/var/www/html/html/verification/

coqdocs-rawvo : $(V_FILES_RAW)
	cp Makefile doc/rawv
	cp Makefile.website doc/rawv
	#make -f Makefile -C doc/rawv type
	#make -f Makefile per.vo -C doc/rawv -j3
	#make -f Makefile -C doc/rawv prop2
	make  -C doc/rawv coqdoc-outputs-vo -j3

coqdoc-raw-htmls : $(coqdocsrawhtml)

doc/verification.pdf : coqdoc-outputs doc/verification.tex
	#cd doc/
	#pdflatex verification.tex
	#bibtex verification
	#pdflatex verification.tex
	#pdflatex verification.tex
	make -C doc/ verification.pdf

type:
	cp universe-type.v universe.v
	#coqc universe.v

prop:
	cp universe-prop.v universe.v
	#coqc universe.v

type2:
	cp universe2_type.v universe2.v
	cp choice-type.v choice.v
	cp per_props_more_type.v per_props_more.v
	#coqc universe2.v

prop2:
	cp universe2_prop.v universe2.v
	cp choice-prop.v choice.v
	cp per_props_more_prop.v per_props_more.v
	#coqc universe2.v
