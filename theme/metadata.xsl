<?xml version="1.0"?>
<!-- SPDX-License-Identifier: CC0-1.0 -->
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:f="http://www.forester-notes.org">

  <xsl:template match="f:month[.='1']">
    <xsl:text>January</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='2']">
    <xsl:text>February</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='3']">
    <xsl:text>March</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='4']">
    <xsl:text>April</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='5']">
    <xsl:text>May</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='6']">
    <xsl:text>June</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='7']">
    <xsl:text>July</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='8']">
    <xsl:text>August</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='9']">
    <xsl:text>September</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='10']">
    <xsl:text>October</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='11']">
    <xsl:text>November</xsl:text>
  </xsl:template>

  <xsl:template match="f:month[.='12']">
    <xsl:text>December</xsl:text>
  </xsl:template>

  <xsl:template match="f:year">
    <xsl:apply-templates />
  </xsl:template>

  <xsl:template match="f:day">
    <xsl:apply-templates />
  </xsl:template>

  <xsl:template match="f:date" mode="date-inner">
    <xsl:apply-templates select="f:month" />
    <xsl:if test="f:day">
      <xsl:text>&#160;</xsl:text>
      <xsl:apply-templates select="f:day" />
    </xsl:if>
    <xsl:if test="f:month">
      <xsl:text>,&#160;</xsl:text>
    </xsl:if>
    <xsl:apply-templates select="f:year" />
  </xsl:template>

  <xsl:template match="f:date[@href]">
    <li class="meta-item">
      <a class="link local" href="{@href}">
        <xsl:apply-templates select="." mode="date-inner" />
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:date[not(@href)]">
    <li class="meta-item">
      <xsl:apply-templates select="." mode="date-inner" />
    </li>
  </xsl:template>

  <xsl:template match="f:authors">
    <xsl:if test="f:author or f:contributor">
      <li class="meta-item">
        <address class="author">
          <xsl:for-each select="f:author">
            <xsl:apply-templates />
            <xsl:if test="position()!=last()">
              <xsl:text>, &#x20;</xsl:text>
            </xsl:if>
          </xsl:for-each>
          <xsl:if test="f:contributor">
            <xsl:text>&#x20;with contributions from&#x20;</xsl:text>
            <xsl:for-each select="f:contributor">
              <xsl:apply-templates />
              <xsl:if test="position()!=last()">
                <xsl:text>,&#x20;</xsl:text>
              </xsl:if>
            </xsl:for-each>
          </xsl:if>
        </address>
      </li>
    </xsl:if>
  </xsl:template>

  <xsl:template match="f:meta[@name='doi']">
    <li class="meta-item">
      <a class="doi link" href="{concat('https://www.doi.org/', .)}">
        <xsl:value-of select="." />
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='orcid']">
    <li class="meta-item">
      <a class="orcid" href="{concat('https://orcid.org/', .)}">
        <xsl:value-of select="." />
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='bibtex']">
    <xsl:variable name="text">
      <xsl:call-template name="preformatted-content" />
    </xsl:variable>
    <pre class="bibtex Agda">
      <xsl:comment>This is a guard for intentional leading blank lines.</xsl:comment>
      <xsl:call-template name="highlight-bibtex">
        <xsl:with-param name="text" select="string($text)" />
      </xsl:call-template>
    </pre>
  </xsl:template>

  <!-- BibTeX highlighting -->
  <xsl:template name="highlight-bibtex">
    <xsl:param name="text" />
    <xsl:variable name="line" select="substring-before(concat($text, '&#10;'), '&#10;')" />
    <xsl:variable name="field" select="normalize-space(substring-before($line, '='))" />
    <xsl:variable name="letters" select="'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'" />
    <xsl:choose>
      <xsl:when test="starts-with(normalize-space($line), '@') and contains(substring-after($line, '{'), ',')">
        <span class="Keyword">
          <xsl:value-of select="substring-before($line, '{')" />
        </span>
        <xsl:text>{</xsl:text>
        <span class="Module">
          <xsl:value-of select="substring-before(substring-after($line, '{'), ',')" />
        </span>
        <xsl:text>,</xsl:text>
        <xsl:value-of select="substring-after(substring-after($line, '{'), ',')" />
      </xsl:when>
      <xsl:when test="$field != '' and contains($letters, substring($field, 1, 1)) and translate($field, concat($letters, '0123456789_-:'), '') = ''">
        <xsl:value-of select="substring-before($line, $field)" />
        <span class="Field">
          <xsl:value-of select="$field" />
        </span>
        <xsl:value-of select="substring-after($line, $field)" />
      </xsl:when>
      <xsl:otherwise>
        <xsl:value-of select="$line" />
      </xsl:otherwise>
    </xsl:choose>
    <xsl:if test="contains($text, '&#10;')">
      <xsl:text>&#10;</xsl:text>
      <xsl:call-template name="highlight-bibtex">
        <xsl:with-param name="text" select="substring-after($text, '&#10;')" />
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <xsl:template match="f:meta[@name='venue']|f:meta[@name='position']|f:meta[@name='institution']|f:meta[@name='source']">
    <li class="meta-item">
      <xsl:apply-templates />
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='external']">
    <li class="meta-item">
      <a class="link external" href="{.}">
        <xsl:value-of select="." />
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='license']">
    <li class="meta-item">
      <a class="link local" href="{concat(/f:tree/@base-url, normalize-space(.))}">
        <xsl:value-of select="normalize-space(.)" />
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='slides']">
    <li class="meta-item">
      <a class="link external" href="{.}">
        <xsl:text>Slides</xsl:text>
      </a>
    </li>
  </xsl:template>

  <xsl:template match="f:meta[@name='video']">
    <li class="meta-item">
      <a class="link external" href="{.}">
        <xsl:text>Video</xsl:text>
      </a>
    </li>
  </xsl:template>

</xsl:stylesheet>
