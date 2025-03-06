<?xml version="1.0"?>
<!-- SPDX-License-Identifier: CC0-1.0 -->
<xsl:stylesheet version="1.0"
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:beamer="http://ctan.org/pkg/beamer"
                xmlns:indenting="jonmsterling:indenting"
                xmlns:f="http://www.jonmsterling.com/jms-005P.xml"
  >

  <!-- The imports must be the first elements in the stylesheet -->
  
  <!-- based on https://git.sr.ht/~jonsterling/forester-base-theme , but changed to imports -->
  <xsl:import href="core.xsl" />
  <xsl:import href="metadata.xsl" />
  <xsl:import href="links.xsl" />
  <xsl:import href="tree.xsl" />

  <xsl:import href="community-overrides.xsl" />
  
  <!-- My layout -->
  <xsl:import href="layout.xsl" />

  <!-- <!-\- My overrides -\-> -->
  <!-- <!-\- Note: Overriding named templates only works when the xlst to be overriden is also imported -\-> -->
  <!-- <xsl:import href="uts-overrides.xsl" /> -->

  <xsl:output method="html" encoding="utf-8" indent="yes" doctype-public="" doctype-system="" />
  
</xsl:stylesheet>
