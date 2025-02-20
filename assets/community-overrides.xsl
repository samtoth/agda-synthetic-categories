<?xml version="1.0"?>
<!-- SPDX-License-Identifier: CC0-1.0 -->
<xsl:stylesheet version="1.0"
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:beamer="http://ctan.org/pkg/beamer"
                xmlns:indenting="jonmsterling:indenting"
                xmlns:f="http://www.jonmsterling.com/jms-005P.xml"
    >
    
  <!-- From https://git.sr.ht/~jonsterling/forest-assets/tree/main/item/jms-forest.xsl -->
  
  <xsl:template match="beamer:*"></xsl:template>
  
  <xsl:template match="indenting:block[ancestor::indenting:block]">
    <div style="margin-left: 1em">
      <xsl:apply-templates />
    </div>
  </xsl:template>
  
  <xsl:template match="indenting:block[not(ancestor::indenting:block)]">
    <div style="margin-left: 1em; margin-bottom: 1em;">
      <xsl:apply-templates />
    </div>
  </xsl:template>
  
  <xsl:template match="indenting:row">
    <div style="min-height: 1em;">
      <xsl:apply-templates />
    </div>
  </xsl:template>
  
  <!-- See also https://github.com/CAIMEOX/caimeox.github.io/blob/main/theme/forest.xsl -->

</xsl:stylesheet>
