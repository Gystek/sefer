(lang dune 3.18)

(name sefer)

(generate_opam_files true)

(source
 (github Gystek/sefer))

(authors "Gustek <gustek@riseup.net>")

(maintainers "Gustek <gustek@riseup.net>")

(license COPYING)

(documentation https://github.com/Gystek/sefer)

(package
 (name sefer)
 (synopsis "Purely functional data-processing")
 (description "A purely functional data-processing language based on iterator combination")
 (depends ocaml)
 (tags
  (language iterators "data processing")))

