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
    a #content { max-width: none !important; }
    a </style>
    d
  }
' README.html

# Don't use a temporary file, or all relative links will break.
# https://github.com/Kozea/WeasyPrint/issues/532
htmlq -f README.html -r 'header' -r 'main > p:first-of-type' | weasyprint -u "" -s <(echo '
  @page {
    size: A4 landscape;
  }

  @font-face {
    font-family: 'DejaVu Sans';
    src: url('file://${pkgs.dejavu_fonts}/share/fonts/truetype/DejaVuSans.ttf') format('truetype');
  }
  @font-face {
    font-family: 'DejaVu Sans Mono';
    src: url('file://${pkgs.dejavu_fonts}/share/fonts/truetype/DejaVuSansMono.ttf') format('truetype');
  }
  @font-face {
    font-family: 'DejaVu Serif';
    src: url('file://${pkgs.dejavu_fonts}/share/fonts/truetype/DejaVuSerif.ttf') format('truetype');
  }
  @font-face {
    font-family: 'Liberation Mono';
    src: url('file://${pkgs.liberation_ttf}/share/fonts/truetype/LiberationMono-Regular.ttf') format('truetype');
  }
  @font-face {
    font-family: 'Liberation Sans';
    src: url('file://${pkgs.liberation_ttf}/share/fonts/truetype/LiberationSans-Regular.ttf') format('truetype');
  }
  @font-face {
    font-family: 'Tex Gyre Cursor';
    src: url('file://${pkgs.gyre-fonts}/share/fonts/truetype/texgyrecursor-regular.otf') format('opentype');
  }
  @font-face {
    font-family: 'Tex Gyre Heros';
    src: url('file://${pkgs.gyre-fonts}/share/fonts/truetype/texgyreheros-regular.otf') format('opentype');
  }
') - README.pdf

mkdir "$out"
cp README.html "$out/README.html"
cp README.pdf "$out/README.pdf"

runHook postInstall
''
