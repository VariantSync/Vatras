{
  sources ? import ./sources.nix,
  system ? builtins.currentSystem,
  pkgs ?
    import sources.nixpkgs {
      overlays = [];
      config = {};
      inherit system;
    },
}:
pkgs.runCommand "Vatras-README" {
  nativeBuildInputs = [
    (pkgs.ruby.withPackages (pkgs: with pkgs; [
      github-pages
      jekyll-theme-cayman
    ]))
    pkgs.htmlq
    pkgs.python3Packages.weasyprint
  ];
} ''
cat > _config.yml <<EOF
theme: jekyll-theme-cayman
baseurl: root
EOF

cp ${../README.md} README.md
JEKYLL_ENV=production PAGES_REPO_NWO=user/repo JEKYLL_BUILD_REVISION= github-pages build

htmlq -f _site/index.html -r '#skip-to-content' -r 'header a' -r footer > README.html
sed -i '
  \|<link .*href="/root/assets/css/style.css?v="| {
    a <style type="text/css">
    r _site/assets/css/style.css
    a </style>
    d
  }
' README.html

# Don't use a temporary file, or all relative links will break.
# https://github.com/Kozea/WeasyPrint/issues/532
htmlq -f README.html -r 'header' -r 'main > p:first-of-type' | weasyprint -u "" -s <(echo '@page { size: A4 landscape; }') - README.pdf

mkdir "$out"
cp README.html "$out/README.html"
cp README.pdf "$out/README.pdf"

runHook postInstall
''
