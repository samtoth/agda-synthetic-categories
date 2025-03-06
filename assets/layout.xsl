<?xml version="1.0"?>
<!-- SPDX-License-Identifier: CC0-1.0 -->
<xsl:stylesheet version="1.0"
 xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
 xmlns:beamer="http://ctan.org/pkg/beamer"
 xmlns:indenting="jonmsterling:indenting"
 xmlns:f="http://www.jonmsterling.com/jms-005P.xml"
 >


<!-- The following is taken from Utensil Song's forest -->

<!-- The following is based on https://git.sr.ht/~jonsterling/forester-base-theme/tree/main/item/tree.xsl -->
<!-- All modifications should mark with comments: st-begin/st-end -->
  <xsl:template match="/">
    <html>
      <head>
        <meta name="viewport" content="width=device-width" />
        <!-- <style> :root { background-color: #262626 !important; }</style> -->
        <link rel="stylesheet" href="style.css" />
        <link rel="stylesheet" href="katex.min.css" />
        <!-- uts-begin -->
        <link rel="stylesheet" href="st-style.css" />
        <!-- uts-end -->
        <script type="text/javascript">
          <xsl:if test="/f:tree/f:frontmatter/f:source-path">
            <xsl:text>window.sourcePath = '</xsl:text>
            <xsl:value-of select="/f:tree/f:frontmatter/f:source-path" />
            <xsl:text>'</xsl:text>
          </xsl:if>
        </script>
        <script type="module" src="forester.js"></script>
        <title>
          <xsl:value-of select="/f:tree/f:frontmatter/f:title" />
        </title>
        <!-- <script src="https://cdn.jsdelivr.net/gh/iconfu/svg-inject@v1.2.3/dist/svg-inject.min.js"></script> -->

        <!-- <script src="uts-forester.js"></script> -->

        <!-- <script src="uts-ondemand.js"></script> -->
        <!-- <script type="module" src="shiki.js"></script>
        <script type="module" src="glsl.js"></script> -->
      </head>
      <body>
        <ninja-keys placeholder="Start typing a note title or ID"></ninja-keys>

        <header class="header">
          <nav class="nav">
            <div class="logo">
              <xsl:if test="not(/f:tree[@root = 'true'])">
                <a href="index.xml" title="Home">
                  <xsl:text>« Home</xsl:text>
                </a>
              </xsl:if>
            </div>
          </nav>
        </header>

        <div id="grid-wrapper">
          <article>
            <xsl:apply-templates select="f:tree" />
          </article>
          <xsl:if test="f:tree/f:mainmatter/f:tree[not(@toc='false')] and not(/f:tree/f:frontmatter/f:meta[@name = 'toc']/.='false')">
            <nav id="toc">
              <div class="block">
                <h1>Table of Contents</h1>
                <xsl:apply-templates select="f:tree/f:mainmatter" mode="toc" />
              </div>
            </nav>
          </xsl:if>
        </div>
      </body>
    </html>
  </xsl:template>
</xsl:stylesheet>
