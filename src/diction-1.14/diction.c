/* Notes */ /*{{{C}}}*//*{{{*/
/*

This program is GNU software, copyright 1997-2017
Michael Haardt <michael@moria.de>.

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, write to the Free Software Foundation, Inc.,
59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

*/
/*}}}*/
/* #includes */ /*{{{*/
#include "config.h"

#include <sys/types.h>
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <locale.h>
#ifdef HAVE_GETTEXT
#include <libintl.h>
#define _(String) gettext(String)
#else
#define _(String) String
#endif
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "getopt.h"
#include "misc.h"
#include "sentence.h"
/*}}}*/
/* types */ /*{{{*/
struct badPhrase
{
  char *phrase;
  size_t phrase_len;
  regex_t phrase_r;
  char *suggest;
  int beginner;
};
/*}}}*/

static int doubleWords=1;
static char phraseLanguage[32];
static struct badPhrase *badPhrases=(struct badPhrase *)0;
static int badPhraseCapacity=0;
static int badPhraseSize=0;
static struct badPhrase *badSuffixes=(struct badPhrase *)0;
static int badSuffixCapacity=0;
static int badSuffixSize=0;
static int sentences,hits;
static int beginner=0;
static int quiet=0;
static int suggest=0;

static void resolve_suggestions(struct badPhrase *phrases, int size) /*{{{*/
{
  int fix;

  /* resolve =phrase explainations */ 
  for (fix=0; fix<size; ++fix)
  {
    if (phrases[fix].suggest && *phrases[fix].suggest=='=')
    {
      int j;

      for (j=0; j<size; ++j)
      {
        if (j!=fix && strcmp(phrases[j].phrase,phrases[fix].suggest+1)==0)
        {
          free(phrases[fix].suggest);
          phrases[fix].suggest=phrases[j].suggest;
          break;
        }
        if (j==size)
        {
          fprintf(stderr,"diction: Warning: Unable to resolve %s.\n",phrases[fix].suggest);
        }
      }
    }
  }
  
}
/*}}}*/
static void loadPhrases(const char *file) /*{{{*/
{
  FILE *fp;
  char ln[1024];
  char *tab,*tab2;
  size_t l;
  int fix,j;

  if ((fp=fopen(file,"r"))==(FILE*)0)
  {
    fprintf(stderr,_("diction: Opening `%s' failed (%s).\n"),file,strerror(errno));
    exit(1);
  }
  while (fgets(ln,sizeof(ln),fp))
  {
    l=strlen(ln);
    if (l && ln[l-1]=='\n') ln[--l]='\0';
    if (ln[0] && ln[0]!='#')
    {
      struct badPhrase *bp;
      int err;

      if (ln[0]==' ')
      {
        if (badPhraseSize==badPhraseCapacity) /* enlarge capacity */ /*{{{*/
        {
          if ((badPhrases=realloc(badPhrases,(badPhraseCapacity=3*(badPhraseCapacity+32))*sizeof(struct badPhrase)))==(struct badPhrase*)0)
          {
            fprintf(stderr,_("diction: out of memory.\n"));
            exit(2);
          }
        }
        /*}}}*/
        bp = &badPhrases[badPhraseSize];
        ++badPhraseSize;
      }
      else
      {
        if (badSuffixSize==badSuffixCapacity) /* enlarge capacity */ /*{{{*/
        {
          if ((badSuffixes=realloc(badSuffixes,(badSuffixCapacity=3*(badSuffixCapacity+32))*sizeof(struct badPhrase)))==(struct badPhrase*)0)
          {
            fprintf(stderr,_("diction: out of memory.\n"));
            exit(2);
          }
        }
        /*}}}*/
        bp = &badSuffixes[badSuffixSize];
        ++badSuffixSize;
      }
      if ((tab=strchr(ln,'\t')))
      {
        *tab='\0';
        ++tab;
      }
      if (tab!=(char*)0 && (tab2=strchr(tab,'\t')))
      {
        *tab2='\0';
        ++tab2;
      }
      else tab2=(char*)0;
      bp->phrase_len=strlen(ln);
      if ((bp->phrase=malloc(bp->phrase_len+1))==(char*)0)
      {
        fprintf(stderr,_("diction: out of memory.\n"));
        exit(2);
      }
      strcpy(bp->phrase,ln);
#if 0
      if ((err=regcomp(&bp->phrase_r,ln,REG_EXTENDED))!=0)
      {
        char errmsg[1024];

        regerror(err,&bp->phrase_r,errmsg,sizeof(errmsg));
        fprintf(stderr,_("diction: Compiling regular expression `%s' failed (%s).\n"),ln,errmsg);
        exit(2);
      }
#endif
      if (tab)
      {
        if ((bp->suggest=malloc(strlen(tab)+1))==(char*)0)
        {
          fprintf(stderr,_("diction: out of memory.\n"));
          exit(2);
        }
        strcpy(bp->suggest,tab);
      }
      else bp->suggest=(char*)0;
      if (tab2)
      {
        bp->beginner=1;
      }
      else
      {
        bp->beginner=0;
      }
    }
  }

  resolve_suggestions(badPhrases, badPhraseSize);
  resolve_suggestions(badSuffixes, badSuffixSize);
}
/*}}}*/
static int cmplen(const void *a_arg, const void *b_arg) /*{{{*/
{
  const struct badPhrase *a=(const struct badPhrase*)a_arg;
  const struct badPhrase *b=(const struct badPhrase*)b_arg;

  return ((int)b->phrase_len)-((int)a->phrase_len);
}
/*}}}*/
static void sort_suggestions(struct badPhrase *phrases, int size) /*{{{*/
{
  qsort(phrases, size, sizeof(*phrases), cmplen);
}
/*}}}*/
static void diction(const char *sent, size_t length, const char *file, int line, int col, int endLine, int endCol) /*{{{*/
{
  const char *lastout=sent;
  const char *s=sent;
  const char *end=sent+length;
  const char *lastWord=(const char*)0;
  const struct badPhrase *badPhraseEnd, *bp;

  if (length==0) return;
  while (s<end)
  {
    int inword;

    inword = (s>sent && isalpha(*(s-1)));

    /* check for bad phrase */ /*{{{*/
    if (inword)
    {
      bp=badSuffixes;
      badPhraseEnd=bp+badSuffixSize;
    }
    else
    {
      bp=badPhrases;
      badPhraseEnd=bp+badPhraseSize;
    }

    for (; bp<badPhraseEnd; ++bp)
    {
      const char *badword,*str;

      badword=bp->phrase;
      if (inword)
      {
        /* suffix match */
        if ((s-2)<sent || !isalpha(*(s-1)) || !isalpha(*(s-2))) continue;
      }
      else      
      {
        /* beginning of sentence or word */
        ++badword;
      }
      str=s;
      while ((*badword==tolower(*str) || *badword==*str) && *badword && *str) { ++badword; ++str; }
      if ((*badword=='\0' && !isalpha(*str)) || (*badword=='~' && isalpha(*str)))
      {
        if (
             (!bp->suggest || (bp->suggest && *bp->suggest!='!'))
             && bp->beginner<=beginner
           )
        {
          ++hits;
          if (lastout==sent)
          {
            if (quiet) printf("%d.%d-%d.%d: ",line,col,endLine,endCol);
            else printf("%s:%d.%d-%d.%d: ",file,line,col,endLine,endCol);
          }
          while (lastout<s) putc(*lastout++,stdout);
          putc('[',stdout);
          while (lastout<str) putc(*lastout++,stdout);
          if (suggest && bp->suggest)
          {
            putc(' ',stdout);
            putc('-',stdout);
            putc('>',stdout);
            putc(' ',stdout);
            fputs(bp->suggest,stdout);
          }
          putc(']',stdout);
        }
        s=str-1;
        break;
      }
    }
    /*}}}*/
    /* check for double words */ /*{{{*/
    if (doubleWords)
    {
      const char *badword,*str;

      if (s>sent && !isalpha(*(s-1)))
      {
        /* move back to end of last word */
        badword=s-1;
        while (badword>sent && !isalpha(*badword)) --badword;
        if (badword>sent)
        {
          /* move back to begin of last word */
          while (badword>sent && isalpha(*badword)) --badword;
          if (!isalpha(*badword)) ++badword;
          str=s;
          while (*badword==*str && badword<s && isalpha(*str)) { ++badword; ++str; }
          if (badword<s && !isalpha(*badword) && !isalpha(*str))
          {
            if (lastout==sent)
            {
              if (quiet) printf("%d-%d:%d-%d: ",line,endLine,col,endCol);
              else printf("%s:%d-%d:%d-%d: ",file,line,endLine,col,endCol);
            }
            while (lastout<s) putc(*lastout++,stdout);
            putc('[',stdout);
            while (lastout<str) putc(*lastout++,stdout);
            if (suggest)
            {
              putc(' ',stdout);
              putc('-',stdout);
              putc('>',stdout);
              putc(' ',stdout);
              fputs(_("Double word."),stdout);
            }
            putc(']',stdout);
            lastWord=s;
            s=str-1;
          }
        }
      }
    }
    /*}}}*/
    ++s;
  }
  ++sentences;
  if (lastout!=sent)
  {
    while (lastout<end) putc(*lastout++,stdout);
    putc('\n',stdout);
    putc('\n',stdout);
  }
}
/*}}}*/
static void print_usage(FILE *handle) /*{{{*/
{
    fputs(_("\
Usage: diction [-b] [-d] [-f file [-n|-L language]] [-q] [file ...]\n\
       diction [--beginner] [--ignore-double-words]\n\
               [--file file [--no-default-file|--language]] [--quiet] [file ...]\n\
       diction --version\n"),handle);
}
/*}}}*/

int main(int argc, char *argv[]) /*{{{*/
{
  int usage=0,c;
  char *userPhrases=(char*)0,*e;
  char defaultPhrases[_POSIX_PATH_MAX];
  static struct option lopts[]=
  {
    { "beginner", no_argument, 0, 'b', },
    { "ignore-double-words", no_argument, 0, 'd' },
    { "suggest", no_argument, 0, 's' },
    { "file", required_argument, 0, 'f' },
    { "help", no_argument, 0, 'h' },
    { "version", no_argument, 0, 'v' },
    { "language", required_argument, 0, 'L' },
    { "quiet", no_argument, 0, 'q' },
    { "no-default-file", no_argument, 0, 'n' },
    { (const char*)0, 0, 0, '\0' }
  };

  /* init locale */ /*{{{*/
  setlocale(LC_ALL,"");
#ifdef HAVE_GETTEXT
  bindtextdomain("diction",LOCALEDIR);
  textdomain("diction");
#endif
  e=getenv("LC_MESSAGES");
  if (e==(char*)0) e=getenv("LC_ALL");
  if (e==(char*)0) e=getenv("LANG");
  if (e)
  {
    strncpy(phraseLanguage,e,sizeof(phraseLanguage)-1);
    phraseLanguage[sizeof(phraseLanguage)-1]='\0';
    if (strstr(phraseLanguage,".."))
    {
      fprintf(stderr,_("diction: Invalid string `..' in default phrase language `%s'.\n"),phraseLanguage);
      exit(2);
    }
    else
    {
      snprintf(defaultPhrases,sizeof(defaultPhrases),SHAREDIR "/diction/%s",e);
      if (access(defaultPhrases,R_OK)!=0)
      {
        phraseLanguage[5]='\0';
        snprintf(defaultPhrases,sizeof(defaultPhrases),SHAREDIR "/diction/%s",phraseLanguage);
        if (access(defaultPhrases,R_OK)!=0)
        {
          phraseLanguage[2]='\0';
          snprintf(defaultPhrases,sizeof(defaultPhrases),SHAREDIR "/diction/%s",phraseLanguage);
          if (access(defaultPhrases,R_OK)!=0)
          {
            strcpy(phraseLanguage,"C");
          }
        }
      }
    }
  }
  else strcpy(phraseLanguage,"C");
  /*}}}*/
  /* parse options */ /*{{{*/
  strcpy(defaultPhrases,SHAREDIR "/diction/");
  while ((c=getopt_long(argc,argv,"bdsf:nL:qh",lopts,(int*)0))!=EOF) switch(c)
  {
    case 'b': beginner=1; break;
    case 'd': doubleWords=0; break;
    case 's': suggest=1; break;
    case 'f': userPhrases=optarg; break;
    case 'n': defaultPhrases[0]='\0'; break;
    case 'L': strncpy(phraseLanguage,optarg,sizeof(phraseLanguage)-1); phraseLanguage[sizeof(phraseLanguage)-1]='\0'; break;
    case 'q': quiet=1; break;
    case 'v': printf("GNU diction " VERSION "\n"); exit(0);
    case 'h': usage=2; break;
    default: usage=1; break;
  }
  if (defaultPhrases[0]) strcat(defaultPhrases,phraseLanguage);
  if (usage==1 || (userPhrases==(char*)0 && defaultPhrases[0]=='\0'))
  {
    print_usage(stderr);
    fputs("\n",stderr);
    fputs(_("Try `diction -h' or `diction --help' for more information.\n"),stderr);
    exit(1);
  }
  if (usage==2)
  {
    print_usage(stdout);
    fputs("\n",stdout);
    fputs(_("Print wordy and commonly misused phrases in sentences.\n\n"),stdout);
    fputs(_("-b, --beginner             complain about typical mistakes of beginners\n"),stdout);
    fputs(_("-d, --ignore-double-words  do not complain about double words\n"),stdout);
    fputs(_("-s, --suggest              suggest better wording\n"),stdout);
    fputs(_("-f, --file                 also read the specified database\n"),stdout);
    fputs(_("-n, --no-default-file      do not read the default phrase file\n"),stdout);
    fputs(_("-L, --language             set document language\n"),stdout);
    fputs(_("-q, --quiet                do not print input file name\n"),stdout);
    fputs(_("-h, --help                 print this message\n"),stdout);
    fputs(_("    --version              print the version\n"),stdout);
    fputs("\n",stdout);
    fputs(_("Report bugs to <michael@moria.de>.\n"),stdout);
    exit(0);
  }
  /*}}}*/
  if (defaultPhrases[0]) loadPhrases(defaultPhrases);
  if (userPhrases) loadPhrases(userPhrases);

  sort_suggestions(badPhrases, badPhraseSize);
  sort_suggestions(badSuffixes, badSuffixSize);

  sentences=0;
  hits=0;
  if (optind==argc) sentence("diction",stdin,"(stdin)",diction,phraseLanguage);
  else while (optind<argc)
  {
    FILE *fp;

    if ((fp=fopen(argv[optind],"r"))==(FILE*)0)
    {
      fprintf(stderr,_("diction: Opening `%s' failed (%s).\n"),argv[optind],strerror(errno));
    }
    else
    {
      sentence("diction",fp,argv[optind],diction,phraseLanguage);
      fclose(fp);
    }
    ++optind;
  }
  if (sentences==0)
  {
    printf(_("No sentences found.\n"));
  }
  else
  {
    if (hits==0) printf(_("No phrases "));
    else if (hits==1) printf(_("1 phrase "));
    else printf(_("%d phrases "),hits);
    if (sentences==1) printf(_("in 1 sentence found.\n"));
    else printf(_("in %d sentences found.\n"),sentences);
  }
  exit(0);
}
/*}}}*/
